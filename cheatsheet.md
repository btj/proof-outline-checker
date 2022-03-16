# Cheat sheet

```python
assert Q[E/x] # Q met E in plaats van x
x = E
assert Q
```

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

```python
assert I # PARTIËLE CORRECTHEID
while C:
    assert I and C
    ...
    assert I
assert I and not C
```

```python
assert I # TOTALE CORRECTHEID
while C:
    oude_variant = V
    assert I and C and V == oude_variant
    ...
    assert I and 0 <= V < oude_variant
assert I and not C
```

## Verantwoordingen voor gevolgtrekkingen

```python
assert True
assert 1 <= 0 + 1 # Z
```

```python
assert True and i < n
assert i + 1 <= n # Z op 2
```

```python
assert i == 0 and 1 <= 0 + 1
assert 1 <= i + 1 # Herschrijven met 1 in 2
```

```python
# Wet LeAntisym: x <= y and y <= x ==> x == y

assert i <= n and n <= i
assert i == n # LeAntisym op 1 en 2
```

```python
# Wet Uitgesteld: b

assert True
assert 0 <= 0 # Uitgesteld # Wet van de gehele getallen
```

```python
# Wet LeAntisym: x <= y and y <= x ==> x == y

assert i <= n and n <= i and res == xs[:i]
assert res == xs[:n] # Herschrijven met LeAntisym op 1 en 2 in 3
```
