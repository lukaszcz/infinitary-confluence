
This is a formalisation of coinductive confluence and normalisation
proofs for the infinitary lambda-calculus. The following theorems are
formalised.
1. Confluence of infinitary beta-bot reduction with any set of
   strongly meaningless terms as meaningless.
2. Normalisation of infinitary beta-bot reduction with any set of
   strongly meaningless terms as meaningless.
3. Confluence of infinitary beta-bot reduction with root-active terms
   as meaningless.
4. Normalisation of infinitary beta-bot reduction with root-active
   terms as meaningless.
5. Confluence of infinitary beta-reduction modulo any set of
   meaningless terms.

All basic definitions are in [defs.v](defs.v). The main results are in
[main.v](main.v). Tested with Coq 8.7.1. The compilation may take
around 5-10 minutes.
