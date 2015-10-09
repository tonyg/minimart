#lang minimart

(struct save (filename body) #:prefab)
(struct contents (filename body) #:prefab)

(actor #:name file-server
       #:state [files (hash)]

       (subscribe (save ($ filename) ($ body))
         #:update [files (hash-set files filename body)]
         #:update-routes)

       (observe-subscribers (contents ($ filename) ?)
         #:level 1
         #:name observed-filenames
         #:set filename)

       (for/advertise [(filename observed-filenames)
                       #:when (hash-has-key? files filename)]
         (contents filename (hash-ref files filename))))

(define (spawn-file-watcher filename)
  (actor #:name observer-of-files
         (observe-advertisers (contents filename ($ file-contents))
           #:name file-contents
           #:set file-contents
           (printf "Contents of ~a: ~v\n" filename file-contents))))

(spawn-file-watcher 'a)
(spawn-file-watcher 'b)
(spawn-file-watcher 'c)
(send (save 'a "first file"))
(send (save 'b "second file"))
(send (save 'c "third file"))
(send (save 'b "second file, second version"))
