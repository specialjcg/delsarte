# Delsarte — contexte projet

## Vision

Formaliser en **Lean 4** le socle du **programme linéaire de Delsarte**, et
s'en servir pour certifier des bornes que la littérature obtient aujourd'hui
par des solveurs numériques non vérifiés.

Deux étages, dans cet ordre :

1. **Le socle réutilisable** — polynômes de Krawtchouk, LP de Delsarte,
   **dualité faible**. C'est elle qui porte tout : *toute* solution duale
   réalisable donne une borne supérieure valide, même non optimale. Le
   certificat se réduit donc à un vecteur de rationnels, et le vérifier à des
   produits scalaires exacts. Chercher est cher, vérifier est bon marché.
2. **Le test de charge** — le **kissing number en dimensions 8 et 24** (240 et
   196 560), par la borne LP d'Odlyzko–Sloane. Atteint : `kissing_eight`,
   `kissing_twentyFour`. En dimension 24 il n'est pas neuf, voir ci-dessous.

Hors périmètre : Viazovska (empilement optimal en dimensions 8 et 24, formalisé
par Math, Inc.). C'est de
l'analyse dure — fonctions modulaires, formules de sommation — sans rapport
avec le schéma certificat/vérification retenu ici.

## Ce qui est déjà pris, vérifié le 15 septembre 2026

À lire avant de croire qu'un créneau est libre. L'absence de publication n'est
pas une preuve d'absence de travail en cours.

- [Sphere-Packing-Lean](https://github.com/math-inc/Sphere-Packing-Lean) —
  Math, Inc., terminé en mars 2026 (commit `1e98fb4` lu). En route vers
  l'unicité en dimension 24, il formalise la borne LP sphérique avec son
  certificat (`delsarte_bound_sphere24_real`, `isDelsarteDual24_f24`),
  `ncard_leechKissingVectors = 196560`, la norme minimale de Leech
  (`leech_norm_lower_bound`), l'unicité de la configuration (Bannai–Sloane),
  du Golay et de Witt. 0 `sorry`, 0 `native_decide`. **Kissing 24 : pris.**
  Kissing 8 : non trouvé. Schéma de Hamming et `A(n,d)` : absents.

- [Formalizing Flag Algebras in Lean](https://arxiv.org/abs/2607.23500) —
  juillet 2026. Compilateur certificat → preuve, sortie SDP traitée comme
  donnée candidate et non comme entrée de confiance, positivité semi-définie
  vérifiée exactement sur ℚ. Sept bornes de type Turán. **Graphes simples
  seulement** : hypergraphes, tournois et permutations restent ouverts.
- [Proof-Carrying Certificates for q-ary Covering Codes in Lean 4](https://arxiv.org/abs/2606.09600)
  — juin 2026. Volume des boules de Hamming, borne sphere-covering, règles de
  produit. **Codes couvrants uniquement.**
- [A Lean-Certified Proof of K₈(4,2) = 23](https://arxiv.org/pdf/2606.16688) —
  juin 2026. Même famille, même limite.

Le LP de Delsarte sur le schéma de Hamming, sa dualité, et `A(n,d)` — le côté
*packing* — ne figurent dans aucun des quatre. C'est le créneau de ce projet.
Le SDP de Schrijver (Terwilliger) : aucune formalisation trouvée. L'arrondi
exact de SDP hors assistant de preuve existe (Dostert–de Laat–Moustrou 2021,
Cohn–de Laat–Leijenhorst 2024) — source de candidats possible, pas
d'antériorité.

## Méthode

Le même invariant que le projet voisin `mathématique/` : **un résultat ne vaut
que par ce qui le vérifie**, et le vérificateur ne doit rien devoir au
programme qui a produit le résultat.

- Le solveur LP/SDP est une **source de candidats**, jamais une autorité. Sa
  sortie flottante est arrondie en rationnels, puis re-vérifiée exactement.
- Un certificat qu'on ne sait pas rejouer indépendamment n'est pas un résultat.
- Les contrôles négatifs comptent autant que les positifs : un vérificateur
  qui n'a jamais rien rejeté n'a rien prouvé.
- Énoncer exactement ce qui est démontré, et rien de plus. Nommer ce qui reste
  non exclu.

## Stack

- **Lean 4** + mathlib. Vérifier ce que mathlib fournit déjà sur la dualité LP
  avant d'en écrire une ligne — c'est le gros du travail de formalisation.
- Solveur externe (LP exact, PPL ou équivalent) pour produire les candidats.
  Il reste hors de la base de confiance.

## Préceptes de code

@/home/jcgouleau/Documents/Obsidian Vault/principe génie logiciel/bonnes-pratiques-code.md
@/home/jcgouleau/Documents/Obsidian Vault/principe génie logiciel/workflow-dev.md
