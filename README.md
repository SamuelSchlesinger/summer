# summer

Extensible sums and products for Haskell.

```haskell
x :: Sum '[Int, Bool, Float]
x = Inj True

y :: Sum '[Int, Float, Bool, Char]
y = weaken x

a :: Bool
a = match y (== 10) (== 0.2) id (== 'x')

x' :: Prod '[Int, Float, Bool, Char]
x' = produce $ \f -> f 10 0.2 True 'x'

y' :: Prod '[Bool, Float]
y' = strengthen x'

a' :: Bool
a' = consume y' (\b f -> b && f == 0.2)
```
