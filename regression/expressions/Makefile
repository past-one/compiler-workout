TESTS=$(basename $(wildcard generated*.expr))

RC = ../../src/rc.opt

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.expr
	@RC_RUNTIME=../../runtime $(RC) $< && cat $@.input | ./$@ > $@.log && diff --strip-trailing-cr $@.log orig/$@.log
	@cat $@.input | $(RC) -i $< > $@.log && diff --strip-trailing-cr $@.log orig/$@.log
	@cat $@.input | $(RC) -s $< > $@.log && diff --strip-trailing-cr $@.log orig/$@.log

clean:
	rm -f *.log *.s *~ $(TESTS)
