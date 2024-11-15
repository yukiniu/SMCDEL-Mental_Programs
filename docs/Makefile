
default: all-svgs


list.txt: $(shell find ../src -type f)
	(cd .. && rg "\\$\(addSvg" src) > list.txt

generator.hs: list.txt collector.sh
	./collector.sh

all-svgs: generator.hs
	stack runghc generator.hs

PHONY = default all-svgs
