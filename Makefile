DUNE=dune

.PHONY: all fracst clean

all: fracst

fracst:
	@${DUNE} build bin/fracst.exe

clean:
	@${DUNE} clean
