all : tactics.vo star.vo defs.vo equality.vo basics.vo beta.vo botred.vo cases.vo weak.vo

tactics.vo : tactics.v
	coqc tactics.v

defs.vo : defs.v
	coqc defs.v

cases.vo : cases.v defs.vo
	coqc cases.v

equality.vo : equality.v defs.vo tactics.vo
	coqc equality.v

star.vo : star.v defs.vo tactics.vo equality.vo
	coqc star.v

basics.vo : basics.v equality.vo defs.vo tactics.vo star.vo equality.vo
	coqc basics.v

beta.vo : beta.v basics.vo
	coqc beta.v

botred.vo : botred.v beta.vo cases.vo
	coqc botred.v

weak.vo : weak.v beta.vo
	coqc weak.v

clean:
	rm -f .*.aux *.vo *.glob
