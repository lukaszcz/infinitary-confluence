all : Reconstr.vo tactics.vo star.vo defs.vo equality.vo basics.vo beta.vo sim.vo botred.vo cases.vo weak.vo crnf.vo root_active.vo nred.vo main.vo

Reconstr.vo : Reconstr.v
	coqc Reconstr.v

tactics.vo : tactics.v Reconstr.vo
	coqc tactics.v

defs.vo : defs.v
	coqc defs.v

cases.vo : cases.v defs.vo tactics.vo
	coqc cases.v

equality.vo : equality.v defs.vo tactics.vo
	coqc equality.v

star.vo : star.v defs.vo tactics.vo equality.vo
	coqc star.v

basics.vo : basics.v equality.vo defs.vo tactics.vo star.vo equality.vo
	coqc basics.v

beta.vo : beta.v basics.vo
	coqc beta.v

sim.vo : sim.v beta.vo cases.vo
	coqc sim.v

botred.vo : botred.v beta.vo sim.vo cases.vo
	coqc botred.v

weak.vo : weak.v beta.vo
	coqc weak.v

crnf.vo : crnf.v weak.vo cases.vo
	coqc crnf.v

nred.vo : nred.v crnf.vo botred.vo sim.vo cases.vo
	coqc nred.v

root_active.vo : root_active.v weak.vo sim.vo
	coqc root_active.v

main.vo : main.v nred.vo root_active.vo botred.vo
	coqc main.v

clean:
	rm -f .*.aux *.vo *.glob
