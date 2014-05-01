all: tmp.csv

clean:
	rm -f tmp.csv
	rm -rf compiled

tmp.csv:
	raco make internal-latency.rkt
	PLTSTDERR=warning racket internal-latency.rkt | tee $@
