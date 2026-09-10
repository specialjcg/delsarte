# Format de certificat dual

Un certificat est un fichier texte. Il ne contient que des **rationnels exacts**.
Aucun flottant n'est accepté, ni à l'écriture ni à la lecture : un solveur qui
produit du flottant doit l'arrondir en rationnel avant d'écrire, et c'est le
rationnel qui est vérifié.

## Grammaire

Une directive par ligne, `clé valeur…`. Les lignes vides et celles commençant
par `#` sont ignorées. Les quatre clés sont obligatoires et apparaissent dans
cet ordre.

```
n <entier ≥ 1>      longueur des mots
q <entier ≥ 2>      taille de l'alphabet
d <entier ≥ 1>      distance minimale visée
y <n rationnels>    multiplicateurs duaux, séparés par des espaces
```

Un rationnel s'écrit `p` ou `p/q`, avec `p` entier signé et `q` entier
strictement positif. Pas de notation décimale, pas d'exposant.

La ligne `y` porte exactement `n` valeurs. La `k`-ième, pour `k = 1 … n`, est le
multiplicateur de la contrainte de Krawtchouk de degré `k`. Il n'y a pas de
contrainte de degré `0` : elle est absorbée dans le terme constant de la borne.

## Exemple

`examples/a-5-3.cert` :

```
n 5
q 2
d 3
y 1 0 0 0 0
```

## Ce qui est vérifié

Avec `K_k(i)` le polynôme de Krawtchouk de degré `k` évalué en `i`
(`Delsarte.krawtchouk n q k i`), le vérificateur contrôle deux familles
d'inégalités :

| | |
|---|---|
| positivité | `0 ≤ y k` pour `1 ≤ k ≤ n` |
| réalisabilité duale | `1 ≤ -Σ_{k=1}^{n} y k · K_k(i)` pour `d ≤ i ≤ n` |

Si les deux passent, alors

```
A(n, q, d) ≤ 1 + Σ_{k=1}^{n} y k · K_k(0)
```

Sur l'exemple : les pentes duales aux distances 3, 4, 5 valent `1, 3, 5`, et la
borne vaut `1 + K_1(0) = 6`. La vraie valeur est `A(5,3) = 4` — le certificat
est valide, pas serré.

**Aujourd'hui la garantie ne couvre que `q = 2`.** Le théorème
`A_le_bound_of_dualCert` est énoncé pour l'alphabet binaire, parce que la
réalisabilité primale n'est démontrée que là (voir `Delsarte/Hamming/Feasible.lean`
et l'issue #13). La clé `q` existe déjà dans le format pour que les certificats
`q`-aires soient écrivables sans changer le format le jour où le théorème
tombera ; en attendant, un certificat avec `q ≠ 2` est bien formé mais aucune
borne ne s'en déduit.

## Base de confiance

Le solveur qui a produit `y` **n'en fait pas partie**. Le vérificateur ne lit
que le fichier, refait tous les produits scalaires sur ℚ, et ne consulte jamais
la trace du solveur, sa valeur objective annoncée, ni son statut de convergence.

La transcription du fichier vers Lean est **manuelle** à ce jour. C'est un choix
assumé plutôt qu'un oubli : la déclaration Lean *est* l'énoncé démontré, donc il
n'y a rien à croire entre le fichier et la preuve. Un parseur déplacerait cette
frontière — il déciderait *quel* énoncé est prouvé — et devrait donc réafficher
`n`, `q`, `d` à côté de la borne. C'est suivi séparément.

Un exécutable ne démontre rien de toute façon. Les `#guard` de
`Delsarte/Certificate/Verify.lean` font tourner le vérificateur compilé sur
l'arithmétique rationnelle réelle à chaque build : c'est le rejeu. La preuve,
elle, reste le théorème Lean.


## Rejeu

```bash
lake exe delsarte-verify Delsarte/Certificate/examples/a-23-7.cert
lake exe delsarte-verify --self-check
```

La première forme parse, exécute le vérificateur et affiche la revendication,
**toujours accompagnée de `n`, `q`, `d`** : une borne sans ses paramètres n'est
pas une borne. La seconde compare chaque fichier livré au certificat défini en
Lean, et échoue s'ils divergent.

L'exécutable **ne démontre rien**. La preuve est le théorème Lean dans
`Delsarte/Certificate/Bounds.lean` ; ceci est le rejeu indépendant.

Lier l'exécutable oblige à compiler mathlib en code natif, il n'est donc pas
construit en CI. Les mêmes vérifications tournent au build via
`Delsarte/Certificate/Files.lean`.

## Strictesse du parseur

Le parseur refuse, et `Delsarte/Certificate/Parse.lean` en fait des contrôles
exécutés au build :

- un décimal `0.5` ou un exposant `1e3` — un format incapable d'exprimer `0.5`
  ne peut pas l'arrondir en silence ;
- un dénominateur nul ;
- un commentaire en fin de ligne de données : seuls les commentaires de ligne
  entière existent, donc un `#` égaré est une erreur et non une queue ignorée ;
- un nombre de valeurs `y` différent de `n` ;
- les directives dans le désordre, en trop, manquantes, ou une clé inconnue ;
- `d = 0`, `d > n`, `q < 2`.

Parser et vérifier sont deux métiers : `y -1 0 0 0 0` est **accepté** par le
parseur et **refusé** par le vérificateur. Le dépôt montre les deux modes
d'échec.
