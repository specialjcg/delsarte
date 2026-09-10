# delsarte

Formalisation en **Lean 4** du socle du programme linéaire de Delsarte, et des
certificats qui en découlent.

## État actuel

| Composant | État |
|---|---|
| Dualité faible pour un LP fini | **démontré** — `Delsarte/LP/WeakDuality.lean` |
| `A(n,d)`, distance minimale, distribution de distances | **démontré** — `Delsarte/Code/Basic.lean` |
| Polynômes de Krawtchouk : définition, valeurs au bord, orthogonalité | **démontré** — `Delsarte/Krawtchouk/Basic.lean` |
| Récurrence à trois termes des Krawtchouk | à faire |
| LP de Delsarte (schéma de Hamming) : assemblage + borne conditionnelle | **démontré** — `Delsarte/Hamming/LP.lean` |
| Réalisabilité primale d'une distribution de distances, **q = 2** | **démontré** — `Delsarte/Hamming/Feasible.lean` |
| Borne de Delsarte sur `A(n,2,d)`, sans hypothèse | **démontré** — `Delsarte/Hamming/Feasible.lean` |
| Réalisabilité primale pour `q > 2` | à faire |
| Vérificateur de certificat dual, exact sur ℚ | **démontré** — `Delsarte/Certificate/Verify.lean` |
| Borne démontrée : `A(5,2,3) ≤ 6` | **démontré** — `Delsarte/Certificate/Verify.lean` |
| Parseur de fichier certificat + exécutable de rejeu | à faire |
| Polynômes de Gegenbauer : définition, normalisation, ancrage Chebyshev | **démontré** — `Delsarte/Gegenbauer/Basic.lean` |
| LP d'Odlyzko–Sloane sur la sphère : borne conditionnelle | **démontré** — `Delsarte/Sphere/LP.lean` |
| Positivité de Schoenberg `Σ G_k(⟨x_i,x_j⟩) ≥ 0`, degrés 0 et 1 | **démontré** — `Delsarte/Sphere/LP.lean` |
| Positivité de Schoenberg, degré quelconque | à faire |
| Kissing number en dimensions 8 et 24 | à faire |

Sur l'alphabet binaire, la chaîne est complète de bout en bout : un vecteur de
rationnels entre, une borne sur `A(n,2,d)` sort, et le solveur qui a produit le
vecteur n'est nulle part dans la preuve. `A(5,2,3) ≤ 6` est démontré — première
borne numérique du dépôt, `#print axioms` propre, sans `native_decide`.

Du côté sphère, la chaîne est montée mais pas fermée. Les Gegenbauer normalisés
par `G_k(1) = 1` sont définis, ancrés à la famille de Chebyshev de mathlib, et
évaluables exactement sur ℚ. La borne d'Odlyzko–Sloane est démontrée, mais
**conditionnellement** à la positivité de Schoenberg `Σ G_k(⟨x_i,x_j⟩) ≥ 0`,
qui n'est établie qu'aux degrés 0 et 1. Un certificat témoin sur le cercle
(coefficients `(1,3,3,1)`, borne 8, vrai maximum 6) montre que les hypothèses du
théorème sont satisfiables — sans quoi une borne conditionnelle ne prouverait
rien.

Ce qui reste : le cas `q > 2`, le parseur de fichier certificat, la positivité
de Schoenberg en degré quelconque — le point dur, qui demande la formule
d'addition des harmoniques sphériques — et le vérificateur de positivité sur
intervalle. Aucune borne en dimension 8 ou 24 n'est établie ici, et le kissing
number reste entièrement devant.

## Pourquoi la dualité faible suffit

Pour un primal `max ⟨c,x⟩` sous `Ax ≤ b`, `x ≥ 0`, tout `y ≥ 0` vérifiant
`Aᵀy ≥ c` donne `⟨c,x⟩ ≤ ⟨b,y⟩` — que `y` soit optimal ou non.

Un certificat se réduit donc à un vecteur de rationnels, et le vérifier à des
produits scalaires exacts. Chercher est cher, vérifier est bon marché. Le
solveur externe qui produit `y` reste **hors de la base de confiance** : sa
sortie flottante est arrondie en rationnels, puis re-vérifiée.

mathlib fournit la machinerie conique (`ProperCone`, dualité, séparation =
Farkas) mais **ni les programmes linéaires ni leur dualité** — les auteurs le
signalent eux-mêmes en TODO dans `Mathlib/Analysis/Convex/Cone/Basic.lean`. La
dualité faible n'en a de toute façon besoin d'aucune : ni topologie, ni
complétude, ni argument de séparation.

## Deux LP distincts

Ils ne se déduisent pas l'un de l'autre. Seule la dualité faible leur est commune.

- **Schéma de Hamming**, pour `A(n,d)` — base de **Krawtchouk**, espace fini.
- **Sphère `S^{d-1}`**, pour le kissing number — base de **Gegenbauer**, espace
  continu, positivité sur `[-1, 1/2]`.

## Périmètre

Hors sujet : Viazovska et l'empilement optimal en dimension 8. Analyse dure —
formes modulaires, formules de sommation — sans rapport avec le schéma
certificat/vérification retenu ici.

## Build

```bash
lake exe cache get   # oléans mathlib pré-compilés
lake build
```

Lean `v4.33.1`, mathlib épinglée sur la même révision. L'épinglage est
délibéré : pas de bot de mise à jour.

## Licence

Apache 2.0, comme mathlib. Voir `LICENSE`.
