# Bewijssilhouettencontroleur

Bewijssilhouettencontroleur kijkt alle bewijssilhouetten in een gegeven Python-programma na op geldigheid. Een bewijssilhouet is een reeks Python-opdrachten waarbij de eerste opdracht gemarkeerd is met `# PRECONDITIE` en de laatste met `# POSTCONDITIE`. De eerste en de laatste opdracht van een bewijssilhouet moeten `assert`-opdrachten zijn. Bewijssilhouettencontroleur kijkt voor elk bewijssilhouet na dat het een geldig bewijs is van de totale correctheid van het programma (wat betekent dat het programma, indien het gestart wordt in een toestand waarin de preconditie waar is, zal eindigen, en wel in een toestand waarin de postconditie waar is), tenzij de eerste regel gemarkeerd is met `# PARTIËLE CORRECTHEID`; in dat geval kijkt Bewijssilhouettencontroleur na dat het een geldig bewijs is van de partiële correctheid van het programma (wat betekent dat het programma, indien het gestart wordt in een toestand waarin de preconditie waar is, ofwel niet zal eindigen, ofwel zal eindigen in een toestand waarin de postconditie waar is).

Meer bepaald kijkt Bewijssilhouettencontroleur na dat het bewijssilhouet toelaat de correctheid van het programma te bewijzen met behulp van het toekenningsaxioma, de regel voor `if`-opdrachten, de regel voor lussen, de regel van het na elkaar uitvoeren, en de regel van het logisch gevolg. Dit betekent dat:
- Voor elke opdracht O in het bewijssilhouet die geen `assert`-opdracht is, nagegaan wordt dat O voorafgegaan wordt door een `assert`-opdracht (genaamd de *preconditie* van O) en gevolgd wordt door een `assert`-opdracht (genaamd de *postconditie* van O).
- Voor elke toekenning `x = E` in het bewijssilhouet nagegaan wordt dat de preconditie van de toekenning de bewering is die je krijgt als je in de postconditie de variabele `x` vervangt door de uitdrukking `E`.

  De verwachte vorm is dus:
  ```python
  assert Q[E/x]
  x = E
  assert Q
  ```
  waarbij we `Q[E/x]` schrijven om de bewering `Q` voor te stellen waarin de variabele `x` vervangen werd door de uitdrukking `E`.

  Bijvoorbeeld:
  ```python
  assert 0 <= 0 <= n
  i = 0
  assert 0 <= i <= n
  ```
- Voor elke opeenvolging van twee `assert`-opdrachten nagegaan wordt dat de tweede bewering een logisch gevolg is van de eerste bewering. Dit betekent dat de tweede bewering waar moet zijn in elke denkbare toestand van de wereld waarin de eerste bewering waar is. De twee beweringen worden respectievelijk het *antecedent* en het *consequent* van de gevolgtrekking genoemd. Zie hieronder voor meer details over hoe Bewijssilhouettencontroleur gevolgtrekkingen nakijkt.

  Bijvoorbeeld:
  ```python
  assert 0 <= n
  assert 0 <= 0 <= n
  ```
  In deze gevolgtrekking noemen we `0 <= n` het antecedent en `0 <= 0 <= n` het consequent. Deze gevolgtrekking is geldig: `0 <= 0 <= n` is waar in elke denkbare toestand van de wereld waarin `0 <= n` waar is.
- Voor elke `if`-opdracht nagegaan wordt
  - dat ze een `else`-tak heeft. Voeg desgevallend `else: pass` toe.
  - dat de preconditie van de `then`-tak gelijk is aan de *conjunctie* van de preconditie P van de `if`-opdracht en de `if`-voorwaarde C, dus dat ze van de vorm `P and C` is,
  - dat de preconditie van de `else`-tak gelijk is aan de conjunctie van de preconditie P van de `if`-opdracht en de negatie van de `if`-voorwaarde C, dus dat ze van de vorm `P and not C` is,
  - en dat de postconditie van de `then`-tak gelijk is aan die van de `else`-tak en aan die van de `if`-opdracht.

  De verwachte vorm is dus
  ```python
  assert P
  if C:
      assert P and C
      ...
      assert Q
  else:
      assert P and not C
      ...
      assert Q
  assert Q
  ```
  Bijvoorbeeld:
  ```python
  assert 0 <= a and 0 <= b
  if a <= b:
      assert 0 <= a and 0 <= b and a <= b
      assert 0 <= a <= b and 0 <= b <= b # Z
      c = b
      assert 0 <= a <= c and 0 <= b <= c
  else:
      assert 0 <= a and 0 <= b and not a <= b
      assert 0 <= a <= a and 0 <= b <= a # Z of Z op 3
      c = a
      assert 0 <= a <= c and 0 <= b <= c
  assert 0 <= a <= c and 0 <= b <= c
  ```
  
- Voor elke lus in een bewijs van partiële correctheid nagegaan wordt
  - dat de preconditie van het luslichaam gelijk is aan de conjunctie van de preconditie I van de lus (die ook dient doet als *lusinvariant*) en de lusvoorwaarde C, dus dat ze van de vorm `I and C` is,
  - dat de postconditie van het luslichaam gelijk is aan de lusinvariant,
  - en dat de postconditie van de lus gelijk is aan de conjunctie van de lusinvariant en de negatie van de lusvoorwaarde, dus dat ze van de vorm `I and not C` is.

  De verwachte vorm is dus
  ```python
  assert I
  while C:
      assert I and C
      ...
      assert I
  assert I and not C
  ```
  Bijvoorbeeld:
  ```python
  assert i + r == n
  while i != n:
      assert i + r == n and i != n
      assert i + 1 + (r - 1) == n # Z op 1
      i = i + 1
      assert i + (r - 1) == n
      r = r - 1
      assert i + r == n
  assert i + r == n and not i != n
  ```

- Voor elke lus in een bewijs van totale correctheid nagegaan wordt
  - dat het luslichaam begint met een toekenning `oude_variant = V` gevolgd door een `assert`-opdracht van de vorm `assert I and C and V == oude_variant` waarbij I de preconditie is van de lus (die ook dienst doet als lusinvariant) en C de lusvoorwaarde. De uitdrukking V wordt de *lusvariant* genoemd.
  - dat het luslichaam eindigt met een opdracht van de vorm `assert I and 0 <= V < oude_variant`,
  - en dat de postconditie van de lus gelijk is aan de conjunctie van de lusinvariant en de negatie van de lusvoorwaarde, dus dat ze van de vorm `I and not C` is.

  De verwachte vorm is dus
  ```python
  assert I
  while C:
      oude_variant = V
      assert I and C and V == oude_variant
      ...
      assert I and 0 <= V < oude_variant
  assert I and not C
  ```
  Bijvoorbeeld:
  ```python
  assert i <= n
  while  i < n:
      oude_variant = n - i
      assert i <= n and i < n and n - i == oude_variant
      assert i < n and n - i == oude_variant and n - (i + 1) < n - i # Z
      assert i + 1 <= n and 0 <= n - (i + 1) < oude_variant # Z op 1 of Herschrijven met 2 in 3
      i = i + 1
      assert i <= n and 0 <= n - i < oude_variant
  assert i <= n and not i < n
  ```

## Controle van gevolgtrekkingen

Hieronder gebruiken we het begrip *conjunct* om elk der leden van een *en*-bewering aan te duiden.
Bijvoorbeeld: de bewering `A and B and C` bestaat uit de drie conjuncten `A`, `B`, en `C`.

Bewijssilhouettencontroleur kijkt een gevolgtrekking na door voor elke conjunct van het consequent na te gaan dat hij ofwel triviaal volgt uit het antecedent, ofwel verantwoord wordt door één van de verantwoordingen vermeld in commentaar na het consequent.

Een conjunct volgt triviaal uit het antecedent als de conjunct een gelijkheid `E == E` is, ofwel als de conjunct identiek is aan één van de conjuncten van het antecedent.

Beschouw bijvoorbeeld de volgende gevolgtrekking:
```python
assert 0 <= a and 0 <= b and not a <= b
assert 0 <= a <= a and 0 <= b <= a # Z of Z op 3
```
De commentaar na het consequent vermeldt twee verantwoordingen, `Z` en `Z op 3`, gescheiden door het woord `of`.
De eerste conjunct `0 <= a` en de derde conjunct `0 <= b` van het consequent volgen triviaal uit het antecedent want ze zijn identiek aan de eerste en de tweede conjunct van het antecedent. De tweede conjunct `a <= a` van het consequent wordt verantwoord door de eerste verantwoording `Z` vermeld in commentaar na het consequent; de vierde conjunct `b <= a` van het consequent wordt verantwoord door de tweede verantwoording `Z op 3`.

We vermelden hieronder de verschillende soorten verantwoordingen die ondersteund worden door Bewijssilhouettencontroleur.

### Z

De verantwoording `Z` verantwoordt conjuncten die afleidbaar zijn uit de
wetten van de gehele getallen (associativiteit en commutativiteit van de optelling, nul is een
neutraal element, de negatie is een tegengestelde).

Bijvoorbeeld:
```python
assert True
assert 1 <= 0 + 1 # Z
```

De conjunct `1 <= 0 + 1` is afleidbaar uit de wetten van de gehele getallen.

### Z op i

De verantwoording `Z op i` verantwoordt conjuncten die afleidbaar zijn
uit de `i`de conjunct van het antecedent met behulp van de wetten van de gehele getallen.

Bijvoorbeeld:
```python
assert i <= n and i < n
assert i + 1 <= n # Z op 2
```
De conjunct `i + 1 <= n` kan afgeleid worden uit de tweede conjunct van het antecedent, nl.
`i < n`, met behulp van
de wetten van de gehele getallen.

### Herschrijven met i in j

De verantwoording `Herschrijven met i in j` is enkel toepasbaar als de `i`de conjunct van het antecedent een gelijkheid `E1 == E2` is.
Ze verantwoordt conjuncten die bekomen kunnen worden door sommige voorkomens van `E1` in de
`j`de conjunct van het antecedent te vervangen door `E2`, en/of door sommige voorkomens van `E2` te vervangen door `E1`.

Bijvoorbeeld:
```python
assert i == 0 and 1 <= 0 + 1
assert 1 <= i + 1 # Herschrijven met 1 in 2
```
Je kan `1 <= i + 1` bekomen door `0` te vervangen door `i` in `1 <= 0 + 1`.

### wet op i1, i2, ...

Je kan *wetten* declareren. Die kan je dan toepassen om gevolgtrekkingen te verantwoorden.

Een wet associeert een naam met een als-dan-bewering. De conjuncten van de *als*-voorwaarde van de als-dan-bewering
noemen we de *premissen* van de wet. De *dan*-voorwaarde noemen we de *conclusie* van de wet.

Bij het toepassen van een wet moet je voor
elke premisse een conjunct van het antecedent opgeven dat met
die premisse overeenkomt. Je kan met die toepassing dan een overeenkomstige instantiatie van de conclusie verantwoorden.

Bijvoorbeeld:
```python
# Wet LeAntisym: x <= y and y <= x ==> x == y

assert i <= n and n <= i
assert i == n # LeAntisym op 1 en 2
```
In deze verantwoording wordt de eerste conjunct `i <= n` van het antecedent opgegeven als overeenkomstige
conjunct voor de eerste premisse `x <= y` van de wet `LeAntisym`, en de tweede conjunct `n <= i` van het
antecedent wordt opgegeven als overeenkomstige conjunct voor de tweede premisse `y <= x`.
Dit verantwoordt de conjunct `i == n` van het consequent; dit is de overeenkomstige instantiatie van de conclusie van de wet.

#### Uitgesteld

Tijdens het opstellen van een bewijssilhouet in Bewijssilhouettencontroleur kan het nuttig zijn, het opstellen van de verantwoording voor een bepaalde gevolgtrekking uit te stellen tot later. Dit kan je gemakkelijk realiseren als volgt:

```python
# Wet Uitgesteld: b

assert True
assert 0 <= 0 # Uitgesteld
```

De wet `Uitgesteld` heeft geen premissen en heeft als conclusie een willekeurige bewering `b`. Deze wet is uiteraard niet logisch geldig; een oplossing die van deze wet gebruik maakt, kan uiteraard niet volledig juist gerekend worden. Echter, als je er niet in slaagt een bepaalde gevolgtrekking te verantwoorden, is het beter dat je ze uitstelt dan dat je een bewijssilhouet indient dat niet aanvaard wordt door Bewijssilhouettencontroleur.

### Herschrijven met wet op i1, i2, ... in j

Als de conclusie van een wet een gelijkheid is, kan je het toevoegen van een conjunct overeenkomstig met de conclusie
van de wet, en het herschrijven met die nieuwe conjunct in een andere conjunct, in één stap doen als volgt:

```python
# Wet LeAntisym: x <= y and y <= x ==> x == y

assert i <= n and n <= i and res == xs[:i]
assert res == xs[:n] # Herschrijven met LeAntisym op 1 en 2 in 3
```
