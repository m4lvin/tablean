default:
	leanproject build

.PHONY: clean showDependencies

clean:
	leanproject clean

dependencies.svg:
	grep -ir import src/*.lean | grep -ve "algebra\|data\|tactic\|order" | awk 'BEGIN {print "digraph G {";} { split($$0,a,".lean:import "); print "\"" substr(a[1],5) "\" -> \"" a[2] "\";" } END { print "}" }'  | dot -Tsvg > $@
