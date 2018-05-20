all : tactics.vo star.vo defs.vo equality.vo basics.vo beta.vo

tactics.vo : tactics.v
	coqc tactics.v

defs.vo : defs.v
	coqc defs.v

equality.vo : equality.v defs.vo tactics.vo
	coqc equality.v

star.vo : star.v defs.vo tactics.vo equality.vo
	coqc star.v

basics.vo : basics.v equality.vo defs.vo tactics.vo equality.vo
	coqc basics.v

beta.vo : beta.v basics.vo
	coqc beta.v

clean:
	rm -f .*.aux *.vo *.glob

