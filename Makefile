default:
	leanproject build

.PHONY: showDependencies

showDependencies:
	grep -ir import src/*.lean | grep -v "data" | grep -v "order" | awk 'BEGIN {print "digraph G {";} { split($$0,a,".lean:import "); print "\"" substr(a[1],5) "\" -> \"" a[2] "\";" } END { print "}" }'  | dot -Tx11
