## Common library code
CODE := $(wildcard src/POCS.v)
CODE += $(wildcard src/Helpers/*.v)
CODE += $(wildcard src/Common/*.v)
CODE += $(wildcard src/Spec/*.v)

## Lab 1: StatDB
CODE += $(wildcard src/Lab1/*.v)

## Lab 2: remap
CODE += $(wildcard src/Lab2/*.v)

COQRFLAGS := -R build POCS

BINS	:= statdb-cli remap-nbd

.PHONY: default
default: $(patsubst %,bin/%,$(BINS)) docs

build/%.v: src/%.v
	@mkdir -p $(@D)
	@rm -f $@
	@ln -s "$(shell pwd)"/$< $@
.PRECIOUS: build/%.v

build/%.v.d: build/%.v $(patsubst src/%.v,build/%.v,$(CODE))
	coqdep -c $(COQRFLAGS) $< > $@
.PRECIOUS: build/%.v.d

-include $(patsubst src/%.v,build/%.v.d,$(CODE))

build/%.vo: build/%.v
	coqc -q $(COQRFLAGS) $<
.PRECIOUS: build/%.vo

.PHONY: coq
coq: $(patsubst src/%.v,build/%.vo,$(CODE))

.PHONY: docs
docs: coq
	@mkdir -p doc
	coqdoc $(COQRFLAGS) -g --interpolate -d doc $(patsubst src/%.v,build/%.v,$(CODE))

.PHONY: %/extract
%/extract: %/Extract.v %/fiximports.py
	@mkdir -p $@
	coqtop $(COQRFLAGS) -batch -noglob -load-vernac-source $<
	./scripts/add-preprocess.sh $@/*.hs

statdb-cli/extract: build/Lab1/StatDbCli.vo
remap-nbd/extract: build/Lab2/RemappedServer.vo

bin/%: %/extract
	mkdir -p $(@D)
	cd $(patsubst %/extract,%,$<) && PATH=$(PATH):"$(shell pwd)"/bin stack build --copy-bins --local-bin-path ../bin

.PHONY: clean
clean:
	rm -rf build
	rm -rf doc
	rm -rf $(foreach d,$(BINS),$(d)/extract)
	rm -rf $(foreach d,$(BINS),$(d)/.stack-work)
	rm -f $(foreach b,$(BINS),bin/$(b))

lab%-handin.tar.gz: clean
	tar cf - `find . -type f | grep -v '^\.*$$' | grep -v '/\.git/' | grep -v 'lab[0-9].*\.tar\.gz'` | gzip > $@

prepare-submit: lab2-handin.tar.gz
