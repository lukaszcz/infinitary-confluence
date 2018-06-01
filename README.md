
This is a formalisation of coinductive confluence and normalisation
proofs for the infinitary lambda-calculus. The following theorems are
formalised.
1. Confluence of infinitary beta-bot reduction for any set of strongly
   meaningless terms.
2. Infinitary normalisation of infinitary beta-bot reduction for any
   set of strongly meaningless terms.
3. Confluence of infinitary beta-bot reduction for root-active terms.
4. Infinitary normalisation of infinitary beta-bot reduction for
   root-active terms.
5. Confluence of infinitary beta-reduction modulo any set of
   meaningless terms.

All basic definitions are in defs.v. The main results are in
main.v. Tested with Coq 8.7.1. The compilation may take around 5-10
minutes.
