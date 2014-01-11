ALL = mod.lib

all: $(ALL)
clean:
	rm -f *.lib *.so

%.lib: %.rs
	rustc --lib $^
	touch $@
