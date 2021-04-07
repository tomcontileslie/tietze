## transformations.g: Semigroup Tietze Transformation Functions
##
## This file implements Tietze transformations 1-4 in
## a user-friendly format.

# TODO decide whether checking equality of words in transformations 1 and 2 is
# reasonable, given that check can run forever.
# If we do keep this format, probably reasonable to create NC versions for
# internal use (e.g. StzGo).

# TIETZE TRANSFORMATION 1: ADD REDUNDANT RELATION
TietzeTransformation1 := function(stz, pair)
  local f, free_fam, r, s, fp_fam, w1, w2, p1, p2;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <pair> should be a pair of LetterRep words.
  # TODO there might be a better input format for second argument.
  #
  # Returns:
  # - nothing, and modifies <stz> in place with <pair> added, if <pair> follows
  #   from the relations already present in <stz>.
  # - ErrorNoReturn if the pair cannot be deduced from current relations.

  # TODO argument checks

  # first check that the pair can be deduced from the other relations, by
  # creating fp semigroup with current relations.
  f        := FreeSemigroup(stz!.gens);  # base free semigroup
  free_fam := FamilyObj(f.1);            # marrow for creating free semigp words
  r        := List(stz!.rels,
                   x -> List(x, y -> AssocWordByLetterRep(free_fam, y)));
  s        := f / r;                    # fp semigroup
  fp_fam   := FamilyObj(s.1);           # marrow for creating fp words
  # words first in free semigroup, then map to fp semigroup:
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);
  p1       := ElementOfFpSemigroup(fp_fam, w1);
  p2       := ElementOfFpSemigroup(fp_fam, w2);
  # check if words are equal in the fp semigroup
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    Add(stz!.rels, pair);
    return;
  else
    ErrorNoReturn("Argument <pair> must be equal in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 2: REMOVE REDUNDANT RELATION
# TODO will this work on stz = rec(gens:=[a], rels:=[[a,a]])?
TietzeTransformation2 := function(stz, index)
  local rels, pair, new_f, new_gens, new_s, free_fam, w1, w2, fp_fam, p1, p2;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <index> should be the index of the relation needing removing in the
  # overall list of relations.
  #
  # Returns:
  # - nothing, and modifies <stz> in place with <index>^th pair removed, if that
  #   pair follows from the relations already present in <stz>.
  # - ErrorNoReturn if the pair to be removed cannot be deduced from the other
  #   relations.
  rels := StructuralCopy(stz!.rels);  # TODO StructuralCopy may not be necessary
  if index > Length(rels) then
    ErrorNoReturn("Second argument <index> must be less than or equal to \n",
                  "the number of relations of the first argument <stz>");
  fi;

  # create hypothetical fp semigroup that would be the result of removing
  # the requested pair
  pair := rels[index];
  Remove(rels, index);
  new_f    := FreeSemigroup(stz!.gens);
  new_gens := GeneratorsOfSemigroup(new_f);
  new_s    := new_f / List(rels,
                           x -> List(x,
                                     y -> Product(List(y,
                                                       z -> new_gens[z]))));

  # create two associative words
  free_fam := FamilyObj(new_f.1);
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);

  # map these words to hypothetical fp semigroup words and check equality
  fp_fam := FamilyObj(new_s.1);
  p1     := ElementOfFpSemigroup(fp_fam, w1);
  p2     := ElementOfFpSemigroup(fp_fam, w2);
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    stz!.rels := rels;
    return;
  else
    ErrorNoReturn("Second argument <index> must point to a relation that is \n",
                  "redundant in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 3: ADD NEW GENERATOR
TietzeTransformation3 := function(stz, word)
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <word> should be a LetterRep word
  #
  # Returns:
  # - nothing, and modifies <stz> in place by adding the relation gen=word,
  #   if the input is reasonable.
  # - ErrorNoReturn if the generator number already exists in stz.

  # TODO could be custom specification of what generator string should be
  # TODO argument checks

  # Add new generator string to the list of gens in similar format
  # N.B. NewGeneratorName is implemented in helpers.g
  Add(stz!.gens, NewGeneratorName(stz!.gens));
  # Add new relation onto the end; Length of stz.gens is number of newest gen
  Add(stz!.rels, [word, [Length(stz!.gens)]]);  # could also be other way around
end;

# TIETZE TRANSFORMATION 4: REMOVE GENERATOR
TietzeTransformation4 := function(stz, gen)
  local found_expr, expr, index, i, decrement;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <gen> should be a pos int (number of generator to be removed)
  #
  # Returns:
  # - nothing, and modifies <stz> in place by removing generator number <gen>,
  #   if this function can find an expression for that generator as a product
  #   of some combination of other generators.
  # - ErrorNoReturn if this is impossible.

  # TODO probably very reasonable to have a NC version where where you specify
  # generator number and word to replace it with, and it just does it without
  # asking.

  # TODO also an intermediate implementation is to have a method for this
  # function which takes in three arguments stz, gen, word and subs word for gen
  # IF it can verify that [gen] = word in stz.

  # argument checks
  if Length(stz!.gens) = 1 then
    ErrorNoReturn("cannot remove only remaining generator",
                  ViewString(stz!.gens[1]));
  fi;
  if gen > Length(stz!.gens) then
    ErrorNoReturn("second argument must be no greater than the total\n",
                  "number of generators");
  fi;

  # find expression for gen
  # TODO this can be less lazy than just looking for an explicit relation
  # NOTE: on the above todo, in fairness we could implement only lazy checking
  # and get the user to add a reduandant relation using Tietze 1, then apply
  # Tietze 4.
  found_expr := false;
  for i in [1 .. Length(stz!.rels)] do
    if stz!.rels[i][1] = [gen] and not gen in stz!.rels[i][2] then
      found_expr := true;
      expr       := ShallowCopy(stz!.rels[i][2]);  # TODO necessary?
      index      := i;
      break;
    elif stz!.rels[i][2] = [gen] and not gen in stz!.rels[i][1] then
      found_expr := true;
      expr       := ShallowCopy(stz!.rels[i][1]);  # TODO necessary?
      index      := i;
      break;
    fi;
  od;

  # check we found one
  if not found_expr then
    ErrorNoReturn("no explicit relation expressing second argument as a\n",
                  "combination of other generators");
  fi;

  # otherwise, sub in expression we found and remove relation we used for gen
  # TODO stop the middle man ext rep conversion
  Remove(stz!.rels, index);
  expr := SEMIGROUPS.WordToExtRepObj(expr);
  Apply(stz!.rels, x -> List(x, SEMIGROUPS.WordToExtRepObj));
  Apply(stz!.rels, x -> List(x, y -> StzSubstitute(y, gen, expr)));
  Apply(stz!.rels, x -> List(x, SEMIGROUPS.ExtRepObjToWord));
  # decrement any gen number beyond the index of the one we removed
  decrement := function(z)
    if z <= gen then  # shouldn't be equal but just in case
      return z;
    else
      return z - 1;
    fi;
  end;
  Apply(stz!.rels, x -> List(x, y -> List(y, decrement)));

  # remove generator.
  Remove(stz!.gens, gen);
end;
