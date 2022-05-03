.PHONY: default clean

default:
	leanproject build

clean:
	leanproject clean

dependencies.svg: src/*.lean
	leanproject import-graph $@
