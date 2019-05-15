This is a formalisation of coinductive confluence and normalisation
proofs for the infinitary lambda calculus. The following theorems are
formalised.
1. Confluence of Böhm reduction over any set of strongly meaningless
   terms.
2. Normalisation of Böhm reduction over any set of strongly
   meaningless terms.
3. Confluence of Böhm reduction over root-active terms.
4. Normalisation of Böhm reduction over root-active terms.
5. Confluence of infinitary beta-reduction modulo any set of
   meaningless terms.

All basic definitions are in [defs.v](defs.v). The main results are in
[main.v](main.v). Tested with Coq 8.7.1, Coq 8.8.1 and Coq 8.9. The
compilation may take around 5-10 minutes.
