INCLUDES= util,x86,ll
SUBMIT := solver.ml alias.ml backend.ml dce.ml constprop.ml team.txt

HWNAME := hw06
TIMESTAMP := $(shell /bin/date "+%Y-%m-%d-%H:%M:%S")
ZIPNAME := $(HWNAME)-submit($(TIMESTAMP)).zip

TEA := "                          _ \n                     ____( )_____ \n     ___            |            |     ____ \n     \  \         _---__________---_  / __ \ \n      \  \       /                  \/ /  \ \ \n_______|  |_____/                    \/____\ \_________________________________ \n       |  |    /                      \     | | \n        \  \__|                        |    | |      _____________ \n         \    |                        |    | |      |           |/\ \n          \   |                        |   / /       |___________|  \ \n           \__\                        /__/ /        \-----------/  / \n               \                      /____/          |---------|__/ \n                \____________________/               / \ _____ / \ \n                 |__________________|                \___________/ \n"

# diffent compilation cmd for Ocaml >= 4.08.1
# otherwise package `num` won't be correctly located
OCAMLNEW := $(shell expr `ocaml --version | sed -e 's/^.* //g' -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/'` \>= 40800)
ifeq "$(OCAMLNEW)" "1"
	LIBS = unix,str
	PKGS = -package num
else
	LIBS = unix,str,nums
	PKGS = 
endif

all: main.native

.PHONY: test
test: main.native
	./main.native --test

.PHONY: main.native
main.native: $(SUBMIT) ast.ml astlib.ml backend.ml driver.ml main.ml runtime.c 
	ocamlbuild -Is $(INCLUDES) $(PKGS) -libs $(LIBS) main.native -use-menhir -yaccflag --explain

.PHONY: main.byte
main.byte: $(SUBMIT) ast.ml astlib.ml backend.ml driver.ml main.ml runtime.c 
	ocamlbuild -tag debug -Is $(INCLUDES) $(PKGS) -libs $(LIBS) main.byte -use-menhir -yaccflag --explain

.PHONY: printanalysis.native
printanalysis.native: $(SUBMIT) ast.ml astlib.ml backend.ml driver.ml main.ml runtime.c
	ocamlbuild -Is $(INCLUDES) $(PKGS) -libs $(LIBS) printanalysis.native -use-menhir -yaccflag --explain

.PHONY: tea
tea:
	@echo $(TEA)

zip: $(SUBMIT)
	zip '$(ZIPNAME)' $(SUBMIT)

.PHONY: clean
clean:
	ocamlbuild -clean
	rm -rf output a.out
