# delsarte

Formalisation en **Lean 4** du socle du programme linéaire de Delsarte, et des
certificats qui en découlent.

## État actuel

| Composant | État |
|---|---|
| Dualité faible pour un LP fini | **démontré** — `Delsarte/LP/WeakDuality.lean` |
| `A(n,d)`, distance minimale, distribution de distances | **démontré** — `Delsarte/Code/Basic.lean` |
| Polynômes de Krawtchouk | à faire |
| LP de Delsarte (schéma de Hamming) | à faire |
| Réalisabilité primale d'une distribution de distances | à faire |
| Vérificateur de certificat sur ℚ | à faire |
| Polynômes de Gegenbauer, LP sur la sphère | à faire |
| Kissing number en dimensions 8 et 24 | à faire |

Seules les définitions et la dualité faible sont démontrées à ce jour. Aucune
borne sur `A(n,d)` ni sur le kissing number n'est établie par ce dépôt.

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
