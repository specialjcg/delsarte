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
| Table de Krawtchouk entière pour un alphabet quelconque | **démontré** — `Delsarte/Certificate/IntTable.lean` |
| Première borne q-aire : `A(11,3,5) ≤ 729`, atteinte par Golay ternaire | **démontré** — `Delsarte/Certificate/Ternary.lean` |
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
| Positivité de Schoenberg en dimension quelconque, **tout degré** | **démontré** — `Delsarte/Sphere/Schoenberg.lean` |
| Produit de Fischer, laplacien, adjonction, reproduction | **démontré** — `Delsarte/Harmonic/Fischer.lean` |
| Polynôme zonal harmonique, tout degré | **démontré** — `Delsarte/Harmonic/Zonal.lean` |
| Kissing number en dimension 24 : **majoration** `≤ 196560` | **démontré** — `Delsarte/Sphere/Kissing.lean` |
| Les 240 racines de E8, séparation vérifiée | **démontré** — `Delsarte/Sphere/E8.lean` |
| **Kissing number en dimension 8 : `= 240`** | **démontré** — `Delsarte/Sphere/E8.lean` |
| Configurations entières génériques : norme commune, séparation, passage à la sphère | **démontré** — `Delsarte/Lattice/Basic.lean` |
| Séparation déduite du minimum d'un réseau (`2⟨u,v⟩ ≤ N`) | **démontré** — `Delsarte/Lattice/Basic.lean` |
| Norme minimale du réseau de Leech (`≥ 32`) | à faire |
| Kissing number en dimension 24, **minoration** (Leech) | à faire |
| Codes linéaires binaires : distance = poids, cardinal, minoration de `A` | **démontré** — `Delsarte/Code/Linear.lean` |
| **`A(23,2,7) = 4096`** — Golay binaire `[23,12,7]` | **démontré** — `Delsarte/Code/Golay.lean` |
| **`A(24,2,8) = 4096`** — Golay étendu `[24,12,8]` | **démontré** — `Delsarte/Code/Golay.lean` |
| **`A(8,2,4) = 16`** — Hamming étendu `[8,4,4]` | **démontré** — `Delsarte/Code/Golay.lean` |
| Autres minorations linéaires (`A(5,2,3)`, `A(6,2,3)`, `A(15,2,5)`…) | à faire |

Sur l'alphabet binaire, la chaîne est complète de bout en bout : un vecteur de
rationnels entre, une borne sur `A(n,2,d)` sort, et le solveur qui a produit le
vecteur n'est nulle part dans la preuve. Trois bornes sont démontrées —
`A(5,2,3) ≤ 4`, `A(13,2,5) ≤ 64`, `A(23,2,7) ≤ 4096` — toutes serrées, la
dernière atteinte par le code de Golay binaire parfait.

La moitié constructive est là depuis `Delsarte/Code/Linear.lean` : trois
majorations deviennent des **égalités**, `A(23,2,7) = 4096`, `A(24,2,8) = 4096`
et `A(8,2,4) = 16`. Ce sont les premières égalités du côté combinatoire ; le
dépôt n'écrivait jusque-là que des `≤` faute de code construit.

Ce qui rend la chose abordable, c'est la linéarité. `MinDistAtLeast` quantifie
sur les paires — 16,7 millions pour Golay, hors de portée du noyau — alors qu'un
code linéaire ramène la distance minimale au poids minimal non nul : 4095 poids.
Et comme pour les 240 racines de E8, l'injectivité n'est pas une hypothèse : deux
messages de même mot donneraient un mot de poids nul, que le même calcul exclut.
Le cardinal `2^k` sort de l'énumération, il n'est pas postulé.

La représentation a été **mesurée avant d'être choisie**. Indexer les messages
par `Fin 12 → ZMod 2` donne l'algèbre la plus propre — l'additivité y est
`add_mul` — et meurt par saturation mémoire après 12 min 42 ; la même chose lue
bit à bit sur un `ℕ` en arithmétique `ZMod 2` coûte 8 min 45 ; en `Bool`, 1 min
16. C'est la troisième qui est écrite, et le prix s'en paie dans `cbit_xor`, où
l'additivité se démontre à la main via `Nat.testBit_xor`.

Les générateurs de Golay ne sont pas tabulés. Le code est cyclique, engendré par
`g(x) = x^11 + x^10 + x^6 + x^5 + x^4 + x^2 + 1`, et les douze lignes sont ses
décalés ; l'extension en longueur 24 ajoute un bit de parité, qui vaut 1 sur
chaque ligne parce que `g` est de poids 7, impair. L'objet mathématique est le
polynôme, pas la matrice.

Contrôles : un seul bit retourné dans la première ligne génératrice fait tomber
le poids minimal à 6 et le vérificateur répond `false` — avec le témoin nommé,
le message `1` ; le code `[8,4,4]` échoue au test `d = 5`, comme il le doit ; et
le mot nul, que l'énumération écarte par une garde explicite, est exhibé pour
que cette garde ne reste pas muette.

La première version compilait en 8 min 40 ici et a été **tuée par la CI** à
quinze minutes. Un résultat qui ne se rejoue que sur la machine de l'auteur n'en
est pas un, donc le coût a dû descendre — sans toucher à une seule preuve. Les
lignes génératrices sont devenues un numéral lu au `Nat.testBit`, que le noyau
accélère, au lieu d'un `match` sur sept littéraux ; `decide +kernel` a supprimé
l'évaluation en double, l'élaborateur puis le noyau ; et surtout l'énumération a
été découpée. Le noyau garde en cache chaque forme normale qu'il calcule et ne
purge jamais ce cache à l'intérieur d'une déclaration : un seul `decide` sur
4096 mots culminait à **22,9 Go**, sur un runner qui en a 16. Huit déclarations
de 512 messages calculent exactement la même chose et culminent à 6,4 Go.

Trois majorations restent sans minoration pour des raisons dites au fichier :
`A(32,2,4) ≤ 2^26` demanderait d'énumérer 67 millions de mots, `A(16,2,6) ≤ 256`
n'est atteinte que par Nordstrom–Robinson, **non linéaire**, et les bornes à 12,
24 ou 40 ont des optima qui ne sont pas des puissances de 2.

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

En dimension quelconque, la positivité de Schoenberg est démontrée **à tout
degré**, ce qui rend la borne d'Odlyzko–Sloane inconditionnelle sur ce point.
Deux preuves indépendantes coexistent aux degrés 2 et 3, et les deux fichiers
élémentaires restent en place : ils portent des témoins que l'argument général ne
donne pas.

Le degré 2 sort d'un Cauchy–Schwarz sur la matrice des moments seconds, et la
borne y est atteinte à la configuration orthonormale. Le degré 3 demande
strictement plus : le Cauchy–Schwarz naïf donne la constante `d` là où il faut
`(d+2)/3`, et il faut donc exploiter la symétrie du tenseur des moments
troisièmes. L'argument est un seul carré développé, celui de la partie
harmonique du tenseur écrite à la main, et la constante obtenue est exacte —
une paire antipodale annule la somme.

Le degré 4 change de nature : la cible de la contraction cesse d'être
irréductible, `C C*` y a deux valeurs propres au lieu d'une, et aucun tenseur
témoin ne se devine plus. L'argument élémentaire s'arrête là, et le degré
arbitraire est traité autrement.

Le mécanisme est un produit scalaire, pas un spectre. `Delsarte/Harmonic/Zonal.lean`
construit le polynôme zonal `Z_k(x, ·)` par la récurrence de Gegenbauer
**homogénéisée** — `t` remplacé par la forme linéaire `⟨x, ·⟩`, le terme constant
multiplié par `‖x‖² ‖y‖²` — et démontre qu'il est harmonique. La preuve tient à
une identité, `∑_i x_i ∂_i Z_(k+1) = (k+1) ‖x‖² Z_k`, dont le pas de récurrence
se réduit à deux égalités entre fractions rationnelles en `k` et `d`.
`Delsarte/Harmonic/Fischer.lean` fournit le produit `⟨p, q⟩ = Σ_α α! p_α q_α`, pour
lequel multiplier par `‖y‖²` est adjoint au laplacien — avec constante exactement
`1` — et pour lequel apparier contre `⟨y, ·⟩^k` **est** l'évaluation, au facteur
`k!` près. La part non dominante de `Z_k(y, ·)` porte un facteur `‖y‖²` et meurt
donc contre `Z_k(x, ·)` harmonique ; ce qui reste est une évaluation :

    ⟨Z_k(x,·), Z_k(y,·)⟩ = lead_k · k! · G_k⟨x,y⟩,   lead_k > 0

La matrice `G_k⟨x_i,x_j⟩` est donc une matrice de Gram divisée par un réel
positif, et la double somme est un carré de norme. Ni harmoniques sphériques, ni
`dim H_k`, ni somme directe orthogonale, ni projecteur : le vecteur harmonique est
**écrit**, pas projeté, et c'est ce qui rend l'information spectrale inutile.
L'estimation initiale de 1500 à 3000 lignes portait sur la construction par
projection ; la construction par récurrence en demande 985, contrôles et prose
compris.

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
séparé, entièrement dans ℚ, sans dépendance d'import vers ℂ. Les certificats ont suivi : `Delsarte/Certificate/IntTable.lean`
construit la table de Krawtchouk entière pour un alphabet quelconque, sans division
— la colonne `0` est une ligne de Pascal **pondérée**, `W(n+1,k) = W(n,k) +
(q-1) W(n,k-1)`, et le pas colonne-à-colonne est `K_(k+1)(i+1) = K_(k+1)(i) -
K_k(i) - (q-1) K_k(i+1)` — donc `decide` reste le vérificateur. La première borne
q-aire est `A(11,3,5) ≤ 729`, **atteinte** par le code de Golay ternaire, avec son
fichier `.cert` replayé comme les autres.

Les définitions binaires n'ont pas bougé d'un octet : les vingt-quatre certificats
déjà démontrés réduisent à travers elles, et changer ce que le noyau réduit serait
un risque pris pour rien. Ce sont leurs *preuves* qui ont disparu, remplacées par
les preuves q-aires composées avec un pont — `krawCol n i = krawColQ n 2 i` — qui
est un théorème et non une identité définitionnelle, donc aussi le contrôle
anti-régression.

Les deux autres hypothèses de `card_le_of_sphereCert` sont maintenant fournies.
Les certificats d'Odlyzko–Sloane ne viennent d'aucun solveur : ils sont forcés par
les écarts complémentaires, c'est-à-dire par les produits scalaires qui se
présentent vraiment hors diagonale — `{0, ±1/2, ±1}` pour E8, `{0, ±1/4, ±1/2,
±1}` pour Leech — chacun racine double à l'intérieur, simple aux bords de
`[-1, 1/2]` :

```
d = 8   f(t) = (t+1)(t+1/2)² t² (t-1/2)                        degré 6
d = 24  f(t) = (t+1)(t+1/2)²(t+1/4)² t² (t-1/4)²(t-1/2)        degré 10
```

Les sept plus onze coefficients de Gegenbauer ont été calculés exactement sur
`ℚ`, et
l'identité `lpPoly d N f = <polynôme factorisé>` est revérifiée par le noyau :
d'où viennent les nombres n'engage personne, `lpPoly_certKiss8` et
`lpPoly_certKiss24` sont la vérification. La même factorisation donne le
certificat d'intervalle gratuitement, un seul carré et un seul couple de
multiplicateurs, `-f = (X+1)(1/2-X)·[X(X+1/2)⋯]²`.

Les deux quotients `(∑ f_k) / f_0` valent **exactement** 240 et 196560 — pas
approximativement, pas avec du jeu. Cette route est donc close par le haut.

En dimension 8 la moitié constructive est là aussi, et
`kissing_eight : IsGreatest (kissingSet 8) 240` est la **première égalité** du
dépôt. Les 240 racines ne sont pas une table collée : elles sont définies par ce
qu'elles sont — les 112 vecteurs `±2e_i ± 2e_j` et les 128 vecteurs à
coordonnées `±1` et nombre pair de `-1` — dans l'échelle doublée qui garde les
coordonnées entières et la norme carrée à 8. Ce que le noyau vérifie est
`⟨u, v⟩ ≤ 4` hors diagonale, par `List.Pairwise` : 28 680 produits scalaires
entiers plutôt que 57 600, une centaine de secondes. `Pairwise` porte sur les
*positions*, donc un vecteur répété donnerait `⟨u, u⟩ = 8 > 4` et échouerait —
la distinction des 240 points n'est pas une hypothèse, c'est une conséquence du
même calcul.

La route structurelle — intégralité du produit scalaire sur E8 et cas d'égalité
de Cauchy–Schwarz — aurait demandé l'argument de parité sur la différence
symétrique de deux parties paires. Le calcul est plus court et vérifie
strictement plus : les 240 vecteurs eux-mêmes, pas un lemme sur un réseau
abstrait qu'il faudrait encore instancier.

Cette plomberie est désormais écrite une fois pour toutes dans
`Delsarte/Lattice/Basic.lean`. Une `IntConfig n M N` est la donnée de `M`
vecteurs entiers de longueur `n`, de norme carrée `N`, séparés par
`2⟨u,v⟩ ≤ N` ; la division par `√N`, le passage à `EuclideanSpace` et la borne
de Gram `≤ 1/2` en découlent génériquement, et `IntConfig.mem_kissingSet` conclut
`M ∈ kissingSet n`. La distinction des vecteurs reste une conséquence et non une
hypothèse : une répétition donnerait `2N ≤ N`, que `0 < N` réfute — même
comptabilité que l'injectivité gratuite des codes linéaires. E8 est reversé dans
cette structure (`e8Config`), et `mem_kissingSet_eight_config` redémontre
`240 ∈ kissingSet 8` par ce second chemin. Les deux preuves ne partagent que la
liste des racines et le `decide` qui la vérifie ; une divergence apparaîtrait sur
240 vecteurs, pas sur 196 560.

Le lemme qui rend la dimension 24 concevable tient en une ligne :
`two_dotp_le_of_min`. Si `u` et `v` ont pour norme carrée `N` et si leur
différence est au moins aussi longue, alors `N ≤ N - 2⟨u,v⟩ + N`, donc
`2⟨u,v⟩ ≤ N`. Pour un réseau, `u - v` est encore un vecteur du réseau, donc
« au moins aussi longue » n'est rien d'autre que le minimum. Une inégalité
remplace les `M(M-1)/2` produits scalaires d'une vérification directe : 28 680
pour E8, que le noyau décide, et 1,9·10¹⁰ pour Leech, qu'il ne décidera jamais.
Le contrôle négatif `two_dotp_le_of_min_fails` montre que l'hypothèse porte :
deux vecteurs de norme carrée 8 dont la différence vaut 4 échouent la
séparation, `2·6 = 12 > 8`.

**En dimension 24, seule la majoration est démontrée** — et pas faute d'un
argument assez fin. `two_dotp_le_of_min` donne `gram ≤ 1/2` dans n'importe quelle
échelle, et pour Leech c'est serré : l'angle minimal vaut exactement 60°, la
différence de deux vecteurs minimaux à `gram = 1/2` étant elle-même minimale. Ce
qui manque est l'hypothèse, pas la conclusion : que tout vecteur non nul de Leech
ait une norme carrée au moins 32. Aucun fait de ce genre n'est démontré ici, le
réseau n'étant pas formalisé. Le dépôt écrit `≤ 196560`, jamais `=`. Que la vraie
valeur soit 196560 est un fait mathématique, pas un fait sur ce dépôt ; ce qui
reste non exclu, c'est toute valeur inférieure à cette borne.

La positivité démontrée est large, pas stricte — une paire antipodale annule la
somme au degré 3 — et elle n'est pas une positivité terme à terme : `G_4` prend
des valeurs négatives en dimension 8, `gegenbauer 8 4 (1/2) < 0` est démontré.

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
