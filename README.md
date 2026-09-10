# delsarte

Formalisation en **Lean 4** du socle du programme linéaire de Delsarte, et des
certificats qui en découlent.

## État actuel

| Composant | État |
|---|---|
| Dualité faible pour un LP fini | **démontré** — `Delsarte/LP/WeakDuality.lean` |
| `A(n,d)`, distance minimale, distribution de distances | **démontré** — `Delsarte/Code/Basic.lean` |
| Polynômes de Krawtchouk : définition, valeurs au bord, orthogonalité | **démontré** — `Delsarte/Krawtchouk/Basic.lean` |
| Récurrence à trois termes des Krawtchouk | **démontré** — `Delsarte/Krawtchouk/Basic.lean` |
| Évaluation des Krawtchouk sans binôme (`krawtchoukRec`) | **démontré** — `Delsarte/Krawtchouk/Basic.lean` |
| LP de Delsarte (schéma de Hamming) : assemblage + borne conditionnelle | **démontré** — `Delsarte/Hamming/LP.lean` |
| Réalisabilité primale d'une distribution de distances, **q = 2** | **démontré** — `Delsarte/Hamming/Feasible.lean` |
| Borne de Delsarte sur `A(n,2,d)`, sans hypothèse | **démontré** — `Delsarte/Hamming/Feasible.lean` |
| Réalisabilité primale pour `q > 2` (caractères complexes) | **démontré** — `Delsarte/Hamming/FeasibleQ.lean` |
| Borne de Delsarte sur `A(n,q,d)` pour tout `q ≥ 1`, sans hypothèse | **démontré** — `Delsarte/Hamming/FeasibleQ.lean` |
| Vérificateur de certificat dual, exact sur ℚ | **démontré** — `Delsarte/Certificate/Verify.lean` |
| Vérificateur de positivité sur intervalle, certificat SOS | **démontré** — `Delsarte/Certificate/Interval.lean` |
| Bornes démontrées : `A(5,2,3) ≤ 4`, `A(13,2,5) ≤ 64`, `A(23,2,7) ≤ 4096` | **démontré** — `Delsarte/Certificate/Bounds.lean` |
| Table de 20 bornes supplémentaires, jusqu'à `A(32,2,4) ≤ 2^26` | **démontré** — `Delsarte/Certificate/Table.lean` |
| Vérification des certificats en entiers, décidée par le noyau | **démontré** — `Delsarte/Certificate/Integer.lean` |
| Solveur LP exact en rationnels (hors base de confiance) | **livré** — `tools/delsarte_lp.py` |
| Parseur de fichier certificat + exécutable de rejeu | **livré** — `Delsarte/Certificate/Parse.lean`, `Main.lean` |
| Polynômes de Gegenbauer : définition, normalisation, ancrages Chebyshev `T` (`d = 2`) et `U` (`d = 4`) | **démontré** — `Delsarte/Gegenbauer/Basic.lean` |
| LP d'Odlyzko–Sloane sur la sphère : borne conditionnelle | **démontré** — `Delsarte/Sphere/LP.lean` |
| Positivité de Schoenberg `Σ G_k(⟨x_i,x_j⟩) ≥ 0`, degrés 0 et 1, toute dimension | **démontré** — `Delsarte/Sphere/LP.lean` |
| Positivité de Schoenberg en dimension 2, tout degré | **démontré** — `Delsarte/Sphere/Dim2.lean` |
| Borne démontrée sur le cercle : au plus 8 points, au moins 6 | **démontré** — `Delsarte/Sphere/Dim2.lean` |
| Positivité de Schoenberg en dimension quelconque, degré 2 | **démontré** — `Delsarte/Sphere/DegreeTwo.lean` |
| Positivité de Schoenberg en dimension quelconque, degré 3 | **démontré** — `Delsarte/Sphere/DegreeThree.lean` |
| Positivité de Schoenberg en dimension quelconque, degré ≥ 4 | à faire — décomposition harmonique |
| Kissing number en dimensions 8 et 24 | à faire |

Sur l'alphabet binaire, la chaîne est complète de bout en bout : un vecteur de
rationnels entre, une borne sur `A(n,2,d)` sort, et le solveur qui a produit le
vecteur n'est nulle part dans la preuve. Trois bornes sont démontrées —
`A(5,2,3) ≤ 4`, `A(13,2,5) ≤ 64`, `A(23,2,7) ≤ 4096` — toutes serrées, la
dernière atteinte par le code de Golay binaire parfait. Seules les majorations
sont établies : aucun code n'est construit, donc rien ici ne s'écrit `= 4096`.

`A(13,2,5) ≤ 64` est le cas qui justifie la machinerie : la borne de Hamming ne
donne que 89. C'est une borne que le programme linéaire gagne et que le
dénombrement élémentaire n'atteint pas.

`Delsarte/Certificate/Table.lean` en ajoute douze, de `A(6,2,3) ≤ 8` à
`A(24,2,8) ≤ 4096` (code de Golay étendu, contre 7216 pour Hamming). Onze sont
serrées ; la douzième, `A(12,2,5) ≤ 40`, ne l'est pas — la vraie valeur est 32 —
et elle est gardée pour cette raison. Une table qui ne montrerait que ses succès
serait de la réclame.

`Table4.lean` et `Table5.lean` en ajoutent huit autres, de `A(16,2,4) ≤ 2048` à
`A(32,2,4) ≤ 2^26`, avec le code atteignant nommé quand il y en a un — Hamming
étendu, Nordstrom–Robinson, Reed–Muller, Golay raccourci. Deux d'entre elles
méritent d'être lues ensemble : `A(31,2,3) ≤ 2^26` est la seule ligne du dépôt où
le programme linéaire ne gagne **rien** — sa borne égale celle de Hamming à
l'unité près, ce qui est la définition d'un code parfait — tandis qu'à
`A(32,2,4)` la même famille gagne presque un facteur deux sur le dénombrement.
`A(26,2,5) ≤ 163840` ne revendique aucune atteinte : la borne est seule.

Ces huit bornes n'existent que parce que les certificats sont désormais vérifiés
en entiers, par réduction du noyau, et non plus par `norm_num` sur des
rationnels : le vérificateur met le certificat à l'échelle de son dénominateur
commun, construit la table de Krawtchouk par récurrence aux différences depuis
une ligne de Pascal, et `decide` fait le reste. Le prix d'une borne est passé de
dizaines de secondes à des millisecondes ; c'est ce qui a rendu `n = 32`
abordable. Aucun `native_decide` : `#print axioms` ne donne toujours que
`propext`, `Classical.choice`, `Quot.sound`.

Les déclarations de ces tables sont **générées** par le solveur puis revérifiées
par Lean, parce que recopier vingt certificats à la main est le bon moyen
d'introduire une faute qu'aucun théorème n'attraperait : un `y` erroné est
généralement irréalisable, mais il peut aussi être réalisable et démontrer une
borne *différente*, plus faible, sans que personne le voie.

Du côté sphère, **la dimension 2 est complète et inconditionnelle** : au plus 8
points unitaires du plan à produits scalaires deux à deux `≤ 1/2`, et au moins 6
par l'hexagone régulier, construit et vérifié. La positivité de Schoenberg y est
démontrée pour tout degré, par une somme de carrés de réels — la transcription
au cercle de l'argument binaire, sans harmoniques sphériques.

En dimension quelconque, la borne d'Odlyzko–Sloane est démontrée mais
**conditionnellement** à cette même positivité, établie aux degrés 0, 1, 2 et 3.
Le degré 2 sort d'un Cauchy–Schwarz sur la matrice des moments seconds, et la
borne y est atteinte à la configuration orthonormale. Le degré 3 demande
strictement plus : le Cauchy–Schwarz naïf donne la constante `d` là où il faut
`(d+2)/3`, et il faut donc exploiter la symétrie du tenseur des moments
troisièmes. L'argument est un seul carré développé, celui de la partie
harmonique du tenseur écrite à la main, et la constante obtenue est exacte —
une paire antipodale annule la somme.

Le degré 4 change de nature, et c'est là que le volet sphère s'arrête. La cible
de la contraction cesse d'être irréductible : `C C*` y a deux valeurs propres au
lieu d'une, l'inégalité passe à trois termes, et il faut le spectre, donc la
décomposition harmonique des tenseurs symétriques. Mathlib ne l'a pas, et
l'estimation honnête est de l'ordre de 1500 à 3000 lignes. Les certificats
d'Odlyzko–Sloane en dimensions 8 et 24 étant de degré 9 ou plus, il n'y a pas
non plus de raccourci par « seulement les degrés utiles » : `dim H_9 = 8008` en
dimension 8.

La condition `f(t) ≤ 0` sur un intervalle, qui n'est pas une somme finie, a son
propre vérificateur : un certificat de sommes de carrés dans le module
quadratique de l'intervalle. Seule la correction est démontrée — le sens
existence (Markov–Lukács) n'a jamais à l'être, puisque la décomposition est
fournie et non dérivée. La borne du cercle passe par ce vérificateur, pas à
côté.

Le cas `q > 2` est démontré. Les caractères de `ℤ/q` sont des racines `q`-ièmes
de l'unité, donc l'argument quitte ℚ : la somme double sur les paires de mots est
`∑_u ‖∑_x χ_u(x)‖²`, un module au carré par vecteur d'indices de poids `k`. La
redescente vers ℚ est explicite — injectivité de `Complex.ofReal`, positivité de
`Complex.normSq`, `Rat.cast` qui reflète l'ordre — et le chaînage binaire reste
séparé, entièrement dans ℚ, sans dépendance d'import vers ℂ. Ce qui n'est **pas**
encore là côté q-aire : les certificats. `Delsarte/Certificate/Integer.lean`
construit la table de Krawtchouk entière par une récurrence binaire, donc aucune
borne ternaire n'est encore établie même si le théorème de solidité les couvre
désormais.

Ce qui reste : la positivité de Schoenberg en degré ≥ 4 — le point dur, qui
demande la décomposition harmonique des tenseurs symétriques. C'est le verrou
unique. Aucune borne en dimension 8 ou 24 n'est établie ici, et le kissing number
reste entièrement devant.

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

Reconstruire toute la bibliothèque, mathlib en cache : **~67 s** (2409 jobs).
Environ 80 % de ce temps est dans les certificats — l'arithmétique rationnelle
exacte, pas les imports. Seuil : si ce chiffre dépasse deux minutes, regarder
d'abord ce qui a été ajouté à `Delsarte/Certificate/`, ensuite seulement les
imports.

Lean `v4.33.1`, mathlib épinglée sur la même révision. L'épinglage est
délibéré : pas de bot de mise à jour. Une montée de version silencieuse de
mathlib changerait ce que les preuves signifient sans que personne ne lise le
diff.

## Rejouer un certificat

```bash
lake exe delsarte-verify Delsarte/Certificate/examples/a-23-7.cert
lake exe delsarte-verify --self-check
```

L'exécutable ne démontre rien : il rejoue. La preuve est le théorème Lean. Le
`--self-check` compare chaque `.cert` livré au certificat défini en Lean, pour
que les deux ne puissent pas diverger en silence.

## Ce que la CI garantit

- Le build échoue si un fichier ne compile pas.
- **`axiom-audit`** : échec si une déclaration sous `Delsarte` dépend
  transitivement d'un axiome hors de `propext, Classical.choice, Quot.sound`.
  Ça attrape `sorry` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`) et tout
  axiome maison, y compris arrivés par un import. Un `sorry` qui compile en
  silence est le pire mode de panne de ce projet.
- Les `#guard` de rejeu tournent au build : le vérificateur est réexécuté sur
  chaque certificat, valide ou non, et un désaccord avec les théorèmes casse la
  CI.
- Les contrôles négatifs sont des théorèmes. Ils échouent au build, pas dans un
  rapport que personne ne lit.
- Chaque `.cert` livré est relu au build et comparé au certificat Lean de même
  nom (`Delsarte/Certificate/Files.lean`). Lake ne suit pas les `.cert` comme
  dépendances — vérifié, pas supposé — donc un build incrémental local peut
  manquer une édition ; un build neuf, ce que fait la CI, ne le peut pas.

## Licence

Apache 2.0, comme mathlib. Voir `LICENSE`.
