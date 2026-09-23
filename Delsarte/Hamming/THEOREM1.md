# Schrijver's Theorem 1, on paper

Issue #45. The blocks (19) of Schrijver's semidefinite program are positive
semidefinite for every binary code. This is the `hblocks` hypothesis of
`Delsarte.Certificate.Schrijver.A_19_6_le_of_relaxation`; its siblings are `hrows`,
the constraints (20), issue #44, and `henc`, the encoding. Since
`Delsarte/Certificate/Relaxation.lean` those are three separate hypotheses rather
than one `Feasible`, so proving this file's claim will visibly remove one.

Reference: A. Schrijver, *New code upper bounds from the Terwilliger algebra and
semidefinite programming*, IEEE Trans. Inf. Theory **51** (2005) 2859–2866.
Equation numbers below are that paper's.

Written in English to match the Lean docstrings it is meant to become. Three
pieces are machine-checked: §4 in `Delsarte/Hamming/Terwilliger.lean`, §1 and the
positivity half of §2 in `Delsarte/Hamming/Positivity.lean`, and the
identification of the program's variables with orbit averages of `M` in
`Delsarte/Hamming/Orbit.lean`. The rest is still only the argument a Lean proof
would follow, and what it does not close is named in *What is not proved* at the
end.

## 0. What is being proved, exactly

`Delsarte/SDP/Sparse.lean` states positivity as a quadratic form, not
spectrally:

```lean
def Feasible (z : ℕ → ℚ) : Prop :=
  (∀ b w, 0 ≤ D.blockForm b z w) ∧ ∀ l, 0 ≤ D.rowForm l z
```

So the target is not "the block matrix has nonnegative eigenvalues" but "for
every `w`, a certain rational expression is `≥ 0`". That is a happy accident:
the proof below produces exactly that, as a sum of squares, and never mentions an
eigenvalue or a C\*-algebra. It has the same shape as
`Delsarte.Hamming.sum_sum_krawtchouk_nonneg` (`Delsarte/Hamming/Feasible.lean:110`)
one level down — there the certificate is `∑ᵤ (∑ₓ χᵤ x)²`, here it is `zᵀ M z`
with `M` a sum of rank-one matrices.

Throughout, `C ⊆ 𝔽₂ⁿ` is a nonempty code, `+` is coordinatewise `XOR`, and
subsets of `{1..n}` are identified with elements of `𝔽₂ⁿ`. `|v|` is the Hamming
weight, `|v ∧ w|` the size of the intersection of the supports.

## 1. The matrix M(C), and why it is positive

For `z ∈ 𝔽₂ⁿ` define the 0/1 vector `χ_z` indexed by `𝔽₂ⁿ`:

    (χ_z)_v = [ z + v ∈ C ].

Then for the matrix `M(C)` of (19), indexed by pairs `(v, w)`,

    M(C)_{v,w} = (1/|C|) · |{ z ∈ C : z + v ∈ C, z + w ∈ C }|
               = (1/|C|) · ( Σ_{z ∈ C} χ_z χ_zᵀ )_{v,w} .

The middle equality is the definition unfolded: the summand at `z` is
`[z+v ∈ C]·[z+w ∈ C]`, which is `1` exactly when `z`, `z+v` and `z+w` all lie in
`C`. So `M(C)` is a nonnegative multiple of a sum of rank-one matrices `χχᵀ`, and

    aᵀ M(C) a = (1/|C|) · Σ_{z ∈ C} ⟨χ_z, a⟩²  ≥  0

for every `a`. No structure of `C` is used — only that the sum is over *some*
set of `z`.

That last remark gives the second family of (19) for free. Summing over the
complement,

    ( Σ_{z ∉ C} χ_z χ_zᵀ )_{v,w} = |{ z ∉ C : z + v ∈ C, z + w ∈ C }|,

which is positive semidefinite by the identical computation, and equals
`M_total − |C|·M(C)` where `M_total` sums over all `z ∈ 𝔽₂ⁿ`. Both families of
(19) are therefore instances of one lemma: *a sum of `χχᵀ` over any index set is
positive semidefinite*. In Lean that is one `Finset.sum_nonneg` over squares.

## 2. Averaging over Sₙ

The program's variables are not the entries of `M(C)` but their orbit averages.
Let `Sₙ` act on `𝔽₂ⁿ` by permuting coordinates and on matrices by
`σ · M = P_σ M P_σᵀ`. Put

    M̃ = (1/n!) · Σ_{σ ∈ Sₙ} P_σ M(C) P_σᵀ .

Each term is positive semidefinite (`aᵀ P_σ M P_σᵀ a = (P_σᵀa)ᵀ M (P_σᵀa) ≥ 0`),
so `M̃` is, being a nonnegative combination of them. This is the only place the
group appears, and it needs nothing about `Sₙ` beyond each `P_σ` being
orthogonal.

`M̃` is `Sₙ`-invariant, so its entry at `(v, w)` depends only on the orbit of the
pair, that is on `(|v|, |w|, |v ∧ w|) = (i, j, t)`. Writing `M^t_{i,j}` for the
0/1 matrix supported on that orbit,

    M̃ = Σ_{i,j,t} x^t_{i,j} · M^t_{i,j},

and `x^t_{i,j}` is the common value of `M̃` on the orbit — the sum of `M(C)` over
the orbit divided by the orbit size

    mult(n, i, j, t) = n! / ( (i−t)! (j−t)! t! (n−i−j+t)! ),

which is where that normalization in `schrijver_algebra.py` comes from. These
`x^t_{i,j}` are the program's variables.

That the two descriptions of `x^t_{i,j}` agree — the orbit average of `M(C)` used
here, and the normalized triple count `xT` that `Delsarte/Hamming/Triples.lean`
defines from `λ^t_{i,j}` — is `lambdaT_eq_orbit_sum`, in
`Delsarte/Hamming/Orbit.lean`. Before it the two were separate definitions in
separate files with nothing relating them. What is still missing here is the
`Sₙ`-invariance that turns the orbit *average* into a *common value* on the orbit,
which is the form §3 uses.

## 3. From M̃ to the blocks

Fix `k` and choose `k` pairwise disjoint pairs of coordinates
`(a₁,b₁), …, (a_k,b_k)`. For `v ⊆ {1..n}` set

    c(v) = Π_{l=1..k} ( [a_l ∈ v] − [b_l ∈ v] )  ∈ {−1, 0, +1},

nonzero exactly when `v` contains exactly one element of each pair. Define, for
`i` in range,

    u_i = Σ_{|v| = i} c(v) · e_v .

Because `c(v) = 0` unless `v` meets every pair, `u_i = 0` unless `i ≥ k`; and
applying the same to complements, unless `i ≤ n − k`. That is exactly the index
range `k ≤ i ≤ n − k` of the block `B_k`, recovered rather than imposed.

Now compute, using the orbit decomposition of §2:

    u_iᵀ M̃ u_j = Σ_{|v|=i, |w|=j} c(v) c(w) · M̃_{v,w}
               = Σ_t x^t_{i,j} · ( Σ_{|v|=i, |w|=j, |v∧w|=t} c(v) c(w) ) .

The inner sum is the content of §4: it equals `2^k · β^t_{i,j,k}`. Granting
that,

    u_iᵀ M̃ u_j = 2^k · Σ_t β^t_{i,j,k} x^t_{i,j} = 2^k · (B_k)_{i,j},

the last equality being the definition of the block in (19). Hence for any
vector `w = (w_k, …, w_{n−k})`, putting `y = Σ_i w_i u_i`,

    wᵀ B_k w = 2^{−k} · Σ_{i,j} w_i w_j · u_iᵀ M̃ u_j = 2^{−k} · yᵀ M̃ y  ≥  0

by §2. **That is Theorem 1.** ∎

Two things are worth noticing. The bound is a single quadratic form evaluated at
one explicit vector — the shape `blockForm` wants. And `u_i` depends on the
choice of pairing while `u_iᵀ M̃ u_j` does not, since `M̃` is `Sₙ`-invariant;
`check_beta.py` turns that into a negative control (a different disjoint pairing
must give the same constant).

## 4. The Gram identity

**Claim.** For `k` disjoint pairs and any `i, j, t`,

    Σ_{|v|=i, |w|=j, |v∧w|=t} c(v) c(w) = 2^k · β^t_{i,j,k},

where

    (7')  β^t_{i,j,k} = Σ_r (−1)^{k−t+r} · C(k, t−r) · mult_{n−2k}(i−k, j−k, r).

*Proof.* Split the coordinates into the `2k` paired ones, `P`, and the `n − 2k`
free ones, `F`. A term is nonzero only if `v` and `w` each pick exactly one
element from each pair, so `|v ∩ P| = |w ∩ P| = k` and therefore `|v_F| = i − k`,
`|w_F| = j − k`.

Let `s` be the number of pairs on which `v` and `w` pick the *same* element.
Then

  * `|v ∧ w| = s + |v_F ∧ w_F|`, since the pairs where they disagree contribute
    nothing to the intersection;
  * `c(v) c(w) = (−1)^{k−s}`, since the factor of a pair is `(+1)(+1)` or
    `(−1)(−1)` when they agree and `(+1)(−1)` when they do not.

Count the configurations on `P` with a given `s`: choose which `s` pairs agree,
`C(k, s)` ways; then each agreeing pair has `2` choices (both take `a_l` or both
take `b_l`) and each disagreeing pair has `2` choices (which of `v`, `w` takes
`a_l`) — so `2^k` in all, independently of `s`. Writing `r = |v_F ∧ w_F|` and
summing over `s + r = t`,

    Σ c(v) c(w) = Σ_r (−1)^{k−(t−r)} · C(k, t−r) · 2^k · mult_{n−2k}(i−k, j−k, r),

and `(−1)^{k−t+r}` is that sign. This is `2^k` times (7'). ∎

The only input is a count of sign patterns; there is no binomial identity to
discharge. That is the reason `beta()` in `tools/schrijver_algebra.py` was
changed to compute (7') rather than (7): it puts the identity `(7) = (7')`, which
*is* a Vandermonde-type binomial identity, off the critical path. The generated
data is unchanged — the two forms agree as integers on all 109290 triples with
`n ≤ 24`.

## 5. What a Lean proof has to do

Architecture (B): prove §1–§4 about the *formula* `β` as defined by (7'), then
bridge to the encoded program once, by calculation.

1. **`sum_chi_sq_nonneg`** — for any `S : Finset (𝔽₂ⁿ)` and any `a`,
   `0 ≤ ∑ z ∈ S, (∑ v, χ z v * a v)^2`. One line, modelled on
   `sum_sum_krawtchouk_nonneg`.
2. **Averaging** — `M̃` positive from `M` positive. A nonnegative combination of
   positive forms; no representation theory.
3. **The Gram identity** of §4, as a statement about `Finset.sum` over
   `powersetCard`. This is the real work: the split `P ⊔ F` and the sign count.
4. **The bridge.** `Data.blockForm b z w` unfolds to
   `qf (base b) w + Σ_u z u / m u * qfAt (byVar u) b w`. With `z` the code's
   `x^t_{i,j}` scaled by the encoding's `m`, this has to be shown equal to a
   positive multiple of `wᵀ B_b w`. The shipped data uses **raw β** — the
   diagonal conjugation `√(C(n,i)C(n,j)/(C(n−2k,i−k)C(n−2k,j−k)))` is applied at
   `tools/schrijver_sdp.py:169`, in float (`** 0.5`), and appears nowhere in
   `tools/schrijver_cert.py`, which is the file the Lean data comes from. So
   this is a scaling calculation, not a change of basis. Being separable
   (`a_i·a_j`), the conjugation would preserve positivity anyway, but it is not
   present in the certificate and does not have to be modelled.

Steps 1 and 2 were expected to be cheap and step 3 to be the substantial one;
that plan held, and what follows reports the outcome. Step 4 is bookkeeping
against `Delsarte/SDP/Schrijver19_6.lean` and cannot be attempted before the
generator's conventions are pinned down in a test.

**State.** Step 3 is formalized in `Delsarte/Hamming/Terwilliger.lean`, and
closed:

* `gramOn_insert_pair`, `gramOn_insert_pair_zero` — peeling one coordinate pair
  off the Gram sum leaves `2·g(t) − 2·g(t+1)`. The sixteen traces of `(v, w)` on
  the pair reduce to four, with signs `+ − − +`. The `t = 0` case is stated
  apart: written `t − 1`, truncated subtraction on `ℕ` would silently readmit
  the two agreeing terms, which are empty there.
* `betaAux_step` — the same recurrence on the coefficient side: Pascal's
  identity, with the `r = t+1` term split off because the two sums do not range
  over the same set.
* `gramOn_eq_pow_mul_betaOn` — the induction on `P`, stated in the *free* sizes
  `i` and `j`, so no subtraction is truncated and no type changes.
* `multOn_card` — the transport along `Finset.orderEmbOfFin`. This is the single
  place that pays for the change of type, which stating §4 in `beta` forces.
* `gram_eq_pow_mul_beta` — §4 over the whole cube, in the paper's notation, for
  `k = |P|` pairwise coordinate-disjoint pairs and `2k ≤ n`.

`check_beta.py` still enumerates all `2ⁿ` subsets for `n ≤ 10`. It is now a
second, independent check rather than the only evidence.

Step 1, and the positivity half of step 2, are formalized in
`Delsarte/Hamming/Positivity.lean`:

* `quadForm_eq_sum_sq`, `quadForm_nonneg` — the matrix of (19) written as a sum
  of rank-one `χχᵀ`, hence a sum of squares. The sum over translations runs over
  an arbitrary set and no proof looks at it, so `S = C` and its complement are
  one lemma rather than two.
* `quadForm_comp`, `sum_smul_quadForm_nonneg` — the positivity half of §2.
  Relabelling the ambient space by a bijection preserves the form, and a
  nonnegative combination of nonnegative forms is nonnegative. No group theory is
  used, only that the weights are nonnegative.

The other half of §2 is **partly** formalized, in `Delsarte/Hamming/Orbit.lean`:

* `lambdaT_eq_orbit_sum` — the sum of the matrix of (19) over the orbit `(i,j,t)`
  is the triple count `λ^t_{i,j}`. The bijection is `(X,Y,Z) ↦ (z, X+Y, X+Z)`,
  fibred over the orbit; translation invariance of the two statistics is
  `hammingDist_translate` and `interDist_translate`. Until this file `M` lived
  over words in `Positivity.lean` and `λ` over triples of codewords in
  `Triples.lean`, with no statement relating them, so the `x^t_{i,j}` were a
  definition standing beside `M` rather than an orbit average of it.

So "step 2" is done in the sense of positivity, done in the sense that the orbit
average is the right object, and **not** done in the sense that the average is
constant on orbits — the `Sₙ`-invariance of `M̃`, which is the form §3 consumes.

A caveat that belongs beside `lambdaT_eq_orbit_sum` rather than against it: both
of its sides are written with the same `interDist`, and its proof never looks
inside that definition, so it holds for any function of the two differences. The
theorem does not pin the statistic to `|(X △ Y) ∩ (X △ Z)|`.
`tools/check_triples.py` is what does, recomputing both sides from bitmask
arithmetic, with guards that corrupt the orbit side only — corrupting both at once
passes vacuously, for that same reason.

`tools/check_quadform.py` pre-checks the §1 identity in exact rational
arithmetic, with two negative controls: a perturbed entry must break it, and an
arbitrary symmetric matrix must be able to drive the form negative.

What remains is step 4, the orbit *constancy* of §2, the assembly of §3 — the
vectors `u_i`, and the identification of `u_iᵀ M̃ u_j` with a block entry — and a
type transport that §5 does not list either, described in §6. §5 enumerates four
steps and that assembly is none of them, so **Theorem 1 itself is not proved**.

## 6. What is not proved

* **`(7) = (7')`.** Checked as integers for every `(n,i,j,k,t)` with `n ≤ 24` by
  `tools/check_beta.py`, which covers every size this repository uses. It is a
  check, not a derivation. It is not on the critical path — `β` is *defined* by
  (7') — but anyone comparing against the paper needs to know it is an
  unverified bridge to the paper's notation.
* **Step 4 of §5, the orbit constancy of §2, and the assembly of §3.** Not
  formalized. The orbit *decomposition* — that the `x^t_{i,j}` are orbit averages
  of `M` and not an unrelated definition — is proved, in
  `Delsarte/Hamming/Orbit.lean`; the *constancy* that §3 consumes is not. The
  assembly — the vectors `u_i`, and `u_iᵀ M̃ u_j = 2^k (B_k)_{i,j}` — is needed
  and is none of the four steps §5 lists; that enumeration is incomplete, not the
  proof. `A_19_6_le_of_relaxation` still carries `hblocks` as a named hypothesis,
  and the module docstring of `Delsarte/Certificate/Schrijver.lean` says so.

  The averaging identity of §2 has a second route, which avoids `M̃` entirely:
  average the *vector* rather than the matrix, so that
  `Σ_σ (P_σ u_i)ᵀ M (P_σ u_j) = n! · Σ_t x^t_{i,j} · 2^k · β^t_{i,j,k}`.
  Positivity of the left side is `sum_smul_quadForm_nonneg` with every weight 1,
  proved; that `x^t_{i,j}` is the orbit sum of `M` is `lambdaT_eq_orbit_sum`,
  proved; the inner sum is `gram_eq_pow_mul_beta`, proved *in its own type* and
  subject to the next bullet. What replaces the invariance of `M̃` is that
  `Σ_σ M[σv,σw]` is constant on the orbit of `(|v|,|w|,|v∧w|)`, a relabelling —
  and that is **not** proved.

  `tools/check_orbit.py` replays the whole route in exact arithmetic for `n ≤ 8`
  with two negative controls. **It is checked, not proved**, and no Lean file
  states the identity itself.

* **A type transport, which no section above costs.** `gram` and
  `gram_eq_pow_mul_beta` in `Delsarte/Hamming/Terwilliger.lean` sum over
  `Finset (Fin n)`; `gramMat` and the matrix of §1 in
  `Delsarte/Hamming/Positivity.lean` sum over `Word n 2`. Calling the inner sum of
  the route above "already proved" is true of the statement *in its own type* and
  silently skips the transport between the two, whose cost is unmeasured.
  `multOn_card` is the precedent — the one place in `Terwilliger.lean` that
  already pays for a change of type — and it is not free.
* **Constraints (20)**, issue #44. Independent of everything above.
