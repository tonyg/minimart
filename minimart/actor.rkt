#lang racket/base

;; TODO: syntax-id-rules: raise-syntax-error on set!, pointing users
;; to the #:update pseudo-action.

;; TODO: enforce presence of #:arguments, and enforce that it declares
;; all the free variables in the actor.

(provide actor
	 observe-gestalt
	 observe-subscribers
	 observe-advertisers
	 advertise
	 subscribe
	 for/advertise
	 for/subscribe
	 define-transition
	 begin-transition
	 noop-transition)

;; (require (for-syntax racket/pretty))
;; (require (for-syntax racket/trace))

(require racket/set)
(require racket/match)

(require (for-syntax racket/match))
(require (for-syntax racket/list))
(require (for-syntax racket/base))
(require (for-syntax syntax/stx))

(require racket/stxparam)
(require racket/splicing)

(require "core.rkt")
(require "gestalt.rkt")

(define-syntax (actor stx)
  (syntax-case stx ()
    [(_actor forms ...)
     (analyze-actor #'_actor #'(forms ...))]))

(define-syntax (observe-gestalt stx) (raise-syntax-error #f "Use of observe-gestalt outside actor form" stx))
(define-syntax (observe-subscribers stx) (raise-syntax-error #f "Use of observe-subscribers outside actor form" stx))
(define-syntax (observe-advertisers stx) (raise-syntax-error #f "Use of observe-advertisers outside actor form" stx))
(define-syntax (advertise stx) (raise-syntax-error #f "Use of advertise outside actor form" stx))
(define-syntax (subscribe stx) (raise-syntax-error #f "Use of subscribe outside actor form" stx))
(define-syntax (for/advertise stx) (raise-syntax-error #f "Use of for/advertise outside actor form" stx))
(define-syntax (for/subscribe stx) (raise-syntax-error #f "Use of for/subscribe outside actor form" stx))

(define-syntax-parameter update-state-struct #f)
(define-syntax-parameter match-state #f)
(define-syntax-parameter update-gestalt #f)

(define-syntax-rule (define-transition head tail ...)
  (define head (begin-transition tail ...)))

(define-syntax (begin-transition stx)
  (syntax-case stx ()
    [(_ forms ...)
     (let ()
       (define result (accumulate-actions (gensym 'begin-transition) '() '() #'(forms ...)))
       ;; (pretty-print `(result ,(syntax->datum result)))
       result)]))

(define (noop-transition state)
  (transition state '()))

(begin-for-syntax

 (define-syntax-rule (define-temporaries [tempvar basestx] ...)
   (match-define (list tempvar ...) (generate-temporaries (list basestx ...))))

 (define (identifier-append ctxt . pieces)
   (and ctxt (datum->syntax ctxt
			    (string->symbol
			     (apply string-append
				    (for/list [(piece pieces)]
				      (symbol->string (if (syntax? piece) (syntax->datum piece) piece))))))))

 (define (analyze-pattern pat-stx)
   (syntax-case pat-stx ($ quasiquote unquote quote)
     ;; Extremely limited support for quasiquoting and quoting
     [(quasiquote (unquote p)) (analyze-pattern #'p)]
     [(quasiquote (p ...)) (analyze-pattern #'(list (quasiquote p) ...))]
     [(quasiquote p) (values #''p #''p #''p '())]
     [(quote p) (values #''p #''p #''p '())]

     [($ v)
      (values #'(?!)
	      #'?
	      #'v
	      (list #'v))]
     [($ v p)
      (let ()
	(define-values (pr g m bs) (analyze-pattern #'p))
	(when (not (null? bs))
	  (raise-syntax-error #f "nested bindings not supported" pat-stx))
	(values #`(?! #,pr)
		g
		#`(and v #,m)
		(list #'v)))]
     [(ctor p ...)
      (let ()
	(define parts (if (identifier? #'ctor) #'(p ...) #'(ctor p ...)))
	(define-values (pr g m bs)
	  (for/fold [(pr '()) (g '()) (m '()) (bs '())] [(p (syntax->list parts))]
	    (define-values (pr1 g1 m1 bs1) (analyze-pattern p))
	    (values (cons pr1 pr)
		    (cons g1 g)
		    (cons m1 m)
		    (append bs1 bs))))
	(if (identifier? #'ctor)
	    (values (cons #'ctor (reverse pr))
		    (cons #'ctor (reverse g))
		    (cons #'ctor (reverse m))
		    bs)
	    (values (reverse pr)
		    (reverse g)
		    (reverse m)
		    bs)))]
     [non-pair
      (if (and (identifier? #'non-pair)
	       (free-identifier=? #'non-pair #'?))
	  (values #'?
		  #'?
		  #'_
		  '())
	  (values #'non-pair
		  #'non-pair
		  #'(== non-pair)
		  '()))]))

 (struct observer
	 (condition level meta-level presence-name set-name set-exp added-name removed-name)
	 #:transparent)

 (struct participator (condition meta-level) #:transparent)

 (define (analyze-actor actor-form-head-stx forms-stx)
   (define actor-name #f)

   ;; (Listof Identifier)
   ;; Names for actor state values. User-supplied identifiers.
   (define statevars '())

   ;; (Listof Identifier)
   ;; Temporaries usable for internal bindings of state values. Computed, fresh identifiers.
   (define statetemps '())

   ;; (Listof Syntax)
   ;; Fragments computing gestalt of the actor. Each is in transition context.
   ;; State bindings and body definitions are in scope.
   (define gestalt-updaters '())

   ;; (Listof Syntax)
   ;; Fragments used to assemble gestalt of the actor. Each is in expression context.
   ;; State bindings and body definitions are in scope.
   (define gestalt-fragments '())

   ;; (Listof (Syntax -> Syntax))
   ;; Sequence of functions generating expressions yielding
   ;; transition-functions for responding to events.
   ;; State bindings and body definitions are in scope.
   (define event-handlers '())

   ;; (Listof Identifier)
   ;; Names for body-definitions representing actions to take on actor bootup.
   (define action-ids '())

   ;; (Listof Syntax)
   ;; Body definition forms.
   (define body-forms '())

   (define-syntax-rule (push! var val) (set! var (cons val var)))
   (define-syntax-rule (push-many! var vals ...) (set! var (append vals ... var)))

   (define (push-statevar! statevar-stx statetemp-stx stateexp-stx)
     (push! statevars statevar-stx)
     (push! statetemps statetemp-stx)
     (push! body-forms #`(define #,statetemp-stx #,stateexp-stx)))

   (define (walk-forms forms-stx)
     (syntax-case forms-stx (observe-gestalt
			     observe-subscribers
			     observe-advertisers
			     advertise
			     subscribe
			     for/advertise
			     for/subscribe)
       [() (build-result)]

       [(#:name name rest ...) ;; TODO: named processes
	(begin (when actor-name (raise-syntax-error #f "duplicate actor #:name" forms-stx))
	       (unless (identifier? #'name)
		 (raise-syntax-error #f "actor #:name must be an identifier" #'name))
	       (set! actor-name #'name)
	       (walk-forms #'(rest ...)))]

       [(#:arguments [arg ...] rest ...) ;; TODO arguments
	(walk-forms #'(rest ...))]

       [(#:state [statevar stateexp] rest ...)
	(begin (define-temporaries [statetemp #'statevar])
	       (push-statevar! #'statevar statetemp #'stateexp)
	       (walk-forms #'(rest ...)))]

       [((observe-gestalt g [pattern body ...] ...) rest ...)
	(begin (analyze-general-observer! #'g #'([pattern (begin-transition body ...)] ...))
	       (walk-forms #'(rest ...)))]

       [((observe-subscribers pat body ...) rest ...)
	(begin (analyze-observation! #'pat #'(body ...) #t)
	       (walk-forms #'(rest ...)))]

       [((observe-advertisers pat body ...) rest ...)
	(begin (analyze-observation! #'pat #'(body ...) #f)
	       (walk-forms #'(rest ...)))]

       [((advertise pat body ...) rest ...)
	(begin (analyze-participation! #'pat #'(body ...) #t)
	       (walk-forms #'(rest ...)))]

       [((subscribe pat body ...) rest ...)
	(begin (analyze-participation! #'pat #'(body ...) #f)
	       (walk-forms #'(rest ...)))]

       [((for/advertise [loopspec ...] pat body ...) rest ...)
	(begin (analyze-group-participation! #'(loopspec ...) #'pat #'(body ...) #t)
	       (walk-forms #'(rest ...)))]

       [((for/subscribe [loopspec ...] pat body ...) rest ...)
	(begin (analyze-group-participation! #'(loopspec ...) #'pat #'(body ...) #f)
	       (walk-forms #'(rest ...)))]

       [(expr rest ...)
	(syntax-case (expand-in-context (gensym 'actor-initialization) #'expr) ()
	  [(head inner-rest ...)
	   (if (or (free-identifier=? #'head #'begin)
		   (free-identifier=? #'head #'begin-transition))
	       (walk-forms #'(inner-rest ... rest ...))
	       (if (ormap (lambda (i) (free-identifier=? #'head i))
			  (syntax->list #'(define-values define-syntaxes begin-for-syntax
					    module module*
					    #%module-begin
					    #%require #%provide)))
		   (begin (push! body-forms #'expr)
			  (walk-forms #'(rest ...)))
		   (begin (push-action! #'expr)
			  (walk-forms #'(rest ...)))))]
	  [non-pair-syntax
	   (begin (push-action! #'expr)
		  (walk-forms #'(rest ...)))])]))

   (define (defbinding name-stx init-name-stx init-exp)
     (list #`(define #,init-name-stx #,init-exp)))

   (define-syntax-rule (analyze-body* self body-stx struct-type o [keyword accessor fieldname] ...)
     (syntax-case body-stx ()
       [(keyword v rest (... ...))
	(if (accessor o)
	    (raise-syntax-error #f (format "duplicate ~a clause" 'keyword) body-stx)
	    (self #'(rest (... ...)) (struct-copy struct-type o [fieldname #'v])))]
       ...
       [other (values o #'other)]))

   (define (analyze-observer-body body-stx o)
     (analyze-body* analyze-observer-body body-stx observer o
		    [#:when observer-condition condition]
		    [#:level observer-level level]
		    [#:meta-level observer-meta-level meta-level]
		    [#:presence observer-presence-name presence-name]
		    [#:name observer-set-name set-name]
		    [#:set observer-set-exp set-exp]
		    [#:added observer-added-name added-name]
		    [#:removed observer-removed-name removed-name]))

   (define (analyze-participator-body body-stx p)
     (analyze-body* analyze-participator-body body-stx participator p
		    [#:when participator-condition condition]
		    [#:meta-level participator-meta-level meta-level]))

   (define (analyze-general-observer! gestalt-stx event-handler-clauses-stx)
     (define-temporaries
       [gestalt-name0 #'general]
       [gestalt-init gestalt-stx])
     (define gestalt-name (identifier-append gestalt-stx 'gestalt: gestalt-name0))
     (push-statevar! gestalt-name gestalt-init #'#f)

     (push! gestalt-updaters
	    #`(begin
		(define #,gestalt-init (label-gestalt #,gestalt-stx #t))
		#:update [#,gestalt-name #,gestalt-init]))

     (push! gestalt-fragments gestalt-name)

     (push! event-handlers
	    (lambda (e-stx)
	      #`(match-state state
			     (let ((filtered-event (filter-event #,e-stx #,gestalt-name)))
			       (if (not filtered-event)
				   #f
				   ((match filtered-event
				      #,@event-handler-clauses-stx
				      [_ #f])
				    state)))))))

   (define (analyze-observation! pat-stx body-stx pub?)
     (define-values (o remaining-stx)
       (analyze-observer-body body-stx (observer #f #f #f #f #f #f #f #f)))
     (match-define
       (observer condition level meta-level presence-name set-name set-exp added-name removed-name)
       o)
     (when (and (not set-name) (or set-exp added-name removed-name))
       (define stx (or set-exp added-name removed-name))
       (raise-syntax-error #f "#:name is required when using #:set, #:added and/or #:removed" stx))
     (define base-temp-name (or set-name presence-name))
     (define-temporaries
       [presence-init presence-name]
       [set-init set-name]
       [set-temp set-name]
       [projector-init base-temp-name]
       [gestalt-init base-temp-name])
     (define projector-name (identifier-append set-name 'projector: set-name))
     (define gestalt-name (identifier-append base-temp-name 'gestalt: base-temp-name))
     (define-values (projector-stx gestalt-stx matcher-stx binders) (analyze-pattern pat-stx))

     (define using-presence? (if presence-name #t #f))
     (define using-set? (if (or set-name added-name removed-name) #t #f))

     (when using-presence?
       (push-statevar! presence-name presence-init #'#f))
     (when using-set?
       (push-statevar! set-name set-init #'(set))
       (push-statevar! projector-name projector-init #'#f))

     (define gestalt-name-available? (or using-presence? using-set?))
     (when gestalt-name-available?
       (push-statevar! gestalt-name gestalt-init #'#f))

     (push! event-handlers
	    (lambda (e-stx)
	      #`(match #,e-stx
		  [(routing-update g)
		   (begin-transition
		     #,@(if using-presence?
			    #`(#:update [#,presence-name
					 (not (gestalt-empty?
					       (gestalt-filter g #,gestalt-name)))])
			    #'())
		     #,@(if using-set?
			    #`((define #,set-temp
				 #,(if set-exp
				       #`(for/set [(e (in-set
						       (gestalt-project/keys g
									     #,projector-name)))]
					   (match-define (list #,@binders) e)
					   #,set-exp)
				       #`(gestalt-project/keys g #,projector-name)))
			       #,@(if added-name
				      #`((define #,added-name (set-subtract #,set-temp
									    #,set-name)))
				      #'())
			       #,@(if removed-name
				      #`((define #,removed-name (set-subtract #,set-name
									      #,set-temp)))
				      #'())
			       #,@(if set-name
				      #`(#:update [#,set-name #,set-temp])
				      #'()))
			    #'())
		     #,@remaining-stx)]
		  [_ noop-transition])))

     (when gestalt-name-available?
       (push! gestalt-updaters
	      #`(begin
		  (define #,projector-init
		    (#,(if pub? #'project-subs #'project-pubs) #,projector-stx
		     #:level #,(or level 0) #:meta-level #,(or meta-level 0)))
		  (define #,gestalt-init (projection->gestalt #,projector-init))
		  #,@(if using-set?
			 #`(#:update [#,projector-name #,projector-init])
			 #'())
		  #,@(if gestalt-name-available?
			 #`(#:update [#,gestalt-name #,gestalt-init])
			 #'()))))

     (push! gestalt-fragments
	    (let ((g (if gestalt-name-available?
			 gestalt-name
			 #`(#,(if pub? #'pub #'sub) #,gestalt-stx
			    #:level #,(+ 1 (or level 0)) #:meta-level #,(or meta-level 0)))))
	      (if condition
		  #`(if #,condition #,g (gestalt-empty))
		  g))))

   (define (analyze-participation! pat-stx body-stx pub?)
     (define-values (p remaining-stx) (analyze-participator-body body-stx (participator #f #f)))
     (match-define (participator condition meta-level) p)
     (define-temporaries [gestalt-name pat-stx])
     (define-values (projector-stx gestalt-stx matcher-stx binders) (analyze-pattern pat-stx))

     (push! gestalt-updaters
	    #`(define #,gestalt-name (#,(if pub? #'pub #'sub) #,gestalt-stx
				      #:meta-level #,(or meta-level 0))))

     (push! gestalt-fragments
	    (if condition
		#`(if #,condition #,gestalt-name (gestalt-empty))
		gestalt-name))

     (when (not (stx-null? remaining-stx))
       (push! event-handlers
	      (lambda (e-stx)
		#`(match #,e-stx
		    [(message #,matcher-stx (== #,(or meta-level 0)) #,pub?)
		     (begin-transition #,@remaining-stx)]
		    [_ noop-transition])))))

   (define (analyze-group-participation! loopspecs-stx pat-stx body-stx pub?)
     (define-values (p remaining-stx) (analyze-participator-body body-stx (participator #f #f)))
     (match-define (participator condition meta-level) p)
     (define-temporaries
       [projector-name pat-stx]
       [gestalt-name pat-stx])
     (define-values (projector-stx gestalt-stx matcher-stx binders) (analyze-pattern pat-stx))
     (unless (stx-null? remaining-stx)
       (raise-syntax-error #f
			   "for/advertise, and for/subscribe cannot install message handlers"
			   remaining-stx))

     (push! gestalt-fragments
	    #`(gestalt-union* (for/list #,loopspecs-stx
				#,@(if condition
				       #`(#:when #,condition)
				       #'())
				(#,(if pub? #'pub #'sub) #,gestalt-stx
				 #:meta-level #,(or meta-level 0))))))

   (define (push-action! action-stx)
     (define-temporaries [temp action-stx])
     (push! action-ids temp)
     (push! body-forms #`(define #,temp #,action-stx)))

   (define (build-result)
     (let ((actor-name (or actor-name #'anonymous-actor)))
       (define state-struct-name
	 (datum->syntax actor-form-head-stx (string->symbol (format "~a-state" (syntax->datum actor-name)))))
       (define-temporaries
	 [e-stx #'event]
	 [state-stx #'state]
	 [update-gestalt-stx #'update-gestalt])
       (define result
	 #`(let ()
	     (struct #,state-struct-name (#,@statevars) #:prefab)
	     (let ()
	       #,@(for/list [(sv statevars)] #`(define-syntax-parameter #,sv #f))
	       (syntax-parameterize
		((update-state-struct
		  (syntax-rules () [(_ v [n e] (... ...))
				    (struct-copy #,state-struct-name v [n e] (... ...))]))
		 (match-state
		  (syntax-rules () [(_ id body (... ...))
				    (match-lambda
				     [(and id (struct #,state-struct-name (#,@statetemps)))
				      (syntax-parameterize
				       (#,@(for/list ([sv statevars] [si statetemps])
					     #`(#,sv (syntax-id-rules () [_ #,si]))))
				       body (... ...))])])))
		(splicing-syntax-parameterize
		 ((update-gestalt (syntax-id-rules () [_ #,update-gestalt-stx]))
		  #,@(for/list ([sv statevars] [si statetemps])
		       #`(#,sv (syntax-id-rules () [_ #,si]))))
		 #,@(reverse body-forms)
		 (define #,update-gestalt-stx
		   (begin-transition
		     #,@gestalt-updaters
		     (routing-update (gestalt-union #,@gestalt-fragments))))
		 (match (#,update-gestalt-stx (#,state-struct-name #,@statevars))
		   [(transition #,state-stx initial-gestalt-actions)
		    (match-define (list (routing-update initial-gestalt))
		      (clean-actions initial-gestalt-actions))
		    (spawn #:boot (begin-transition #,@(reverse action-ids))
			   (procedure-rename
			    (lambda (#,e-stx #,state-stx)
			      (and #,e-stx
				   (sequence-transitions (transition #,state-stx '())
							 #,@(map (lambda (p) (p e-stx))
								 (reverse event-handlers)))))
			    '#,actor-name)
			   #,state-stx
			   initial-gestalt)]))))))
       ;; (pretty-print `(result ,(syntax->datum result)))
       result))

   (walk-forms forms-stx))

 (define (expand-in-context context-id stx)
   (local-expand stx
		 (list context-id)
		 (syntax->list #'(quote quote-syntax lambda case-lambda let-values letrec-values
				  begin begin0 set! with-continuation-mark if #%app #%expression
				  define-values define-syntaxes begin-for-syntax #%require #%provide
				  #%variable-reference))))

 (define (accumulate-actions context-id action-ids final-forms forms)
   (syntax-case forms ()
     [()
      #`(match-state state
	  #,@(reverse final-forms)
	  (transition state (list #,@(reverse action-ids))))]

     [(#:run-transition exp rest ...)
      #`(match-state state
	  #,@(reverse final-forms)
	  (sequence-transitions (transition state (list #,@(reverse action-ids)))
				exp
				(begin-transition rest ...)))]

     [(#:update [statevar stateval] rest ...)
      #`(match-state state
	  #,@(reverse final-forms)
	  (sequence-transitions (transition (update-state-struct state [statevar stateval])
					    (list #,@(reverse action-ids)))
				(begin-transition rest ...)))]

     [(#:update-routes rest ...)
      #`(match-state state
	  #,@(reverse final-forms)
	  (sequence-transitions (transition state (list #,@(reverse action-ids)))
				update-gestalt
				(begin-transition rest ...)))]

     [(expr rest ...)
      (syntax-case (expand-in-context context-id #'expr) ()
	[(head inner-rest ...)
	 (if (or (free-identifier=? #'head #'begin)
		 (free-identifier=? #'head #'begin-transition))
	     (accumulate-actions context-id
				 action-ids
				 final-forms
				 (append (syntax->list #'(inner-rest ...)) #'(rest ...)))
	     (if (ormap (lambda (i) (free-identifier=? #'head i))
			(syntax->list #'(define-values define-syntaxes begin-for-syntax
					  module module*
					  #%module-begin
					  #%require #%provide)))
		 (accumulate-actions context-id
				     action-ids
				     (cons #'expr final-forms)
				     #'(rest ...))
		 (accumulate-action #'expr
				    context-id
				    action-ids
				    final-forms
				    #'(rest ...))))]
	[non-pair-syntax
	 (accumulate-action #'expr
			    context-id
			    action-ids
			    final-forms
			    #'(rest ...))])]))

 (define (accumulate-action action-stx context-id action-ids final-forms remaining-forms)
   (define-temporaries [temp action-stx])
   (accumulate-actions context-id
		       (cons temp action-ids)
		       (cons #`(define #,temp #,action-stx) final-forms)
		       remaining-forms)))

;;; Local Variables:
;;; eval: (put 'begin-transition 'scheme-indent-function 0)
;;; eval: (put 'observe-gestalt 'scheme-indent-function 1)
;;; eval: (put 'observe-subscribers 'scheme-indent-function 1)
;;; eval: (put 'observe-advertisers 'scheme-indent-function 1)
;;; eval: (put 'subscribe 'scheme-indent-function 1)
;;; eval: (put 'advertise 'scheme-indent-function 1)
;;; End:
