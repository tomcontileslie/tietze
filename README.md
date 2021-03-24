# tietze
A sandbox for GAP code implementing something like SimplifyPresentation for FP Semigroups.

Part of the St Andrews VIP in Mathematical Software under supervision by [Prof. James Mitchell](https://github.com/james-d-mitchell/).

Contributors: [Tom Conti-Leslie](https://github.com/tomcontileslie) and [Ben Spiers](https://github.com/bspiers).

## Functions currently implemented

### In [`gap/helpers.g`](gap/helpers.g):

- FpSemigroupToStzObj(s)
  - Arguments:
    - s, a fp semigroup
  - Output: a "stz object" (a record with components `gens` and `rels`).
  - Comments: just a placeholder for now. Should think about what we want `gens` to be (currently generators of the original fp semigroup `s`, but
    could instead be generators of the overlying free semigroup, or just strings representing those generators, which is what Ben has done in gap/stzobj.g).
    Rels are currently stored as flat lists of generator numbers (e.g. `[1, 2, 1]` for `aba`).
- StzObjToFpSemigroup(stz)
  - Arguments:
    - stz, a "stz object" as above
  - Output: a fp semigroup
  - Comments: creates a new fp semigroup with generators and relations as given in stz. Note that if `s` is an fp semigroup, then
    `StzObjToFpSemigroup(FpSemigroupToStzObj(s))` should return an fp semigroup isomorphic to `s` but not equal.
- StzSimplify(word)
  - Arguments:
    - word, an ExtRep-format (i.e. [generator, power]) assoc word
  - Output: a new word, equal to the input but compressed so that any sublist `[gen1, pow1, gen1, pow2]` becomes `[gen1, pow1+pow2]`.
- StzSubstitute(word, gen, prod)
  - Arguments:
    - word, an ExtRep-format word
    - gen, a pos int indicating which generator needs to be swapped out
    - prod, an ExtRep-format word which should replace each occurence of the generator gen
  - Output: a new word where every occurence of the old generator `gen` has been replaced with the word `prod`.
- NewGeneratorName(names)
  - Arguments:
    - names, a list of strings
  - Output: a string representing a new generator name, attempted in a similar format to the generator names given in argument `names`.
- StzReplaceSubword(stz, subword, newword)
  - Arguments:
    - stz, an "stz object" (different to above - here it is a list stz = [gens, rels])
    - subword, a LetterRep associative word (flat list of gens)
    - newword, a LetterRep assoc word that should replace subword (and be lex smaller?)
  - Output: none (modifies stz in place)
  - Comments: simply applies the next function to every word in the relations list.
- StzReplaceSubwordRel(letterrep, subword, newword)
  - Arguments:
    - letterrep, a LetterRep associative word
    - subword, a LetterRep associative word
    - newword, a LetterRep assoc word that should replace subword
  - Output: a new LetterRep associative word with every occurence of subword replaced with newword
  - Comments: gets applied recursively.

### In [`gap/transformations.g`](gap/transformations.g):

- TietzeTransformation1(stz, pair)
  - Arguments:
    - stz, a "stz object" (here a record with components `gens` and `rels`)
    - pair, a pair of LetterRep associative words to be added to the list of relations
  - Output: none (modifies stz in place)
  - Comments: meant to be user-friendly. Checks whether the new pair is redundant given the relations already in stz. Refuses to add the relation if it is not
    redundant (NB this may run forever). Usage example in [this log](https://github.com/tomcontileslie/tietze/blob/fc87021a77c214d464b135caea35a8db76c97318/logs/2021-03-24.md).
- TietzeTransformation2(stz, index)
  - Arguments:
    - stz, a "stz object" like in prev function
    - index, a pos int indicating which relation in the list of relations needs to be removed
  - Output: none (modifies stz in place)
  - Comments: meant to be user-friendly. Checks whether the relation that is being removed can be deduced from all the other relations. Refuses to remove
    the relation if not. Usage example in the same log file as above.
