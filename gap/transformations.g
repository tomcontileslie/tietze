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
  local s, free_fam, w1, w2, fp_fam, p1, p2;
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

  # first check that the pair can be deduced from the other relations
  # create fp semigroup with current relations
  s := StzObjToFpSemigroup(stz);
  # retrieve free semigroup obj family and create two associative words
  # corresponding to word
  free_fam := FamilyObj(FreeSemigroupOfFpSemigroup(s).1);
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);
  # send these words to their fp counterparts
  fp_fam := FamilyObj(s.1);
  p1     := ElementOfFpSemigroup(fp_fam, w1);
  p2     := ElementOfFpSemigroup(fp_fam, w2);
  # check if words are equal in the fp semigroup
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    Add(stz.rels, pair);
    return;
  else
    ErrorNoReturn("Argument <pair> must be equal in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 2: REMOVE REDUNDANT RELATION
# TODO will this work on stz = rec(gens:=[a], rels:=[[a,a]])?
TietzeTransformation2 := function(stz, index)
  local rels, s, pair, new_stz, new_s, free_fam, w1, w2, fp_fam, p1, p2;
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
  rels := ShallowCopy(stz.rels);  # TODO ShallowCopy may not be necessary
  if index > Length(rels) then
    ErrorNoReturn("Second argument <index> must be less than or equal to \n",
                  "the number of relations of the first argument <stz>");
  fi;

  # create current fp semigroup
  # then create hypothetical fp semigroup that would be the result of removing
  # the requested pair
  s    := StzObjToFpSemigroup(stz);
  pair := rels[index];
  Remove(rels, index);
  new_stz      := ShallowCopy(stz);  # TODO may be unneccesary
  new_stz.rels := rels;
  new_s        := StzObjToFpSemigroup(new_stz);

  # create two associative words
  free_fam := FamilyObj(FreeSemigroupOfFpSemigroup(s).1);
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);

  # map these words to hypothetical fp semigroup words and check equality
  fp_fam := FamilyObj(new_s.1);
  p1     := ElementOfFpSemigroup(fp_fam, w1);
  p2     := ElementOfFpSemigroup(fp_fam, w2);
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    stz.rels := new_stz.rels;
    return;
  else
    ErrorNoReturn("Second argument <index> must point to a relation that is \n",
                  "redundant in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 3: ADD NEW GENERATOR
TietzeTransformation3 := function(stz, word)
  local new_strs, n, new_rels, f, free_fam, free_rels;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <word> should be a LetterRep word
  #
  # Returns:
  # - nothing, and modifies <stz> in place by adding the relation gen=word,
  #   if the input is reasonable.
  # - ErrorNoReturn if the generator number already exists in stz.

  # TODO could be custom specification of what generator string should be

  # find new generator with similar label to ones used so far
  # NewGeneratorName is in gap/helpers.g
  new_strs := List(stz.gens, ViewString);
  n        := Length(new_strs);
  Add(new_strs, NewGeneratorName(new_strs));

  # Add new relation to list
  new_rels  := StructuralCopy(stz.rels);  # TODO check copy
  Add(new_rels, [word, [n + 1]]);         # could also be other way around

  # We have a new generator so need to re-create fp semigroup generators.
  # Start with free semigroup, translate relations into relations in that free
  # semigroup, then quotient out and retrieve generators
  f := FreeSemigroup(new_strs);
  # find family for marrow transplant
  free_fam  := FamilyObj(f.1);
  free_rels := List(new_rels,
                    x -> List(x, y -> AssocWordByLetterRep(free_fam, y)));
  # quotient and get generators
  stz.gens := GeneratorsOfSemigroup(f / free_rels);
  stz.rels := new_rels;
end;

# TIETZE TRANSFORMATION 4: REMOVE GENERATOR
TietzeTransformation4 := function(stz, gen)
  local found_expr, expr, index, i;
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
  if Length(stz.gens) = 1 then
    ErrorNoReturn("cannot remove only remaining generator",
                  ViewString(stz.gens[1]));
  fi;
  if gen > Length(stz.gens) then
    ErrorNoReturn("second argument must be no greater than the total\n",
                  "number of generators");
  fi;

  # find expression for gen
  # TODO this can be less lazy than just looking for an explicit relation
  # NOTE: on the above todo, in fairness we could implement only lazy checking
  # and get the user to add a reduandant relation using Tietze 1, then apply
  # Tietze 4.
  found_expr := false;
  for i in [1 .. Length(stz.rels)] do
    if stz.rels[i][1] = [gen] and not gen in stz.rels[i][2] then
      found_expr := true;
      expr       := ShallowCopy(stz.rels[i][2]);  # TODO necessary?
      index      := i;
      break;
    elif stz.rels[i][2] = [gen] and not gen in stz.rels[i][1] then
      found_expr := true;
      expr       := ShallowCopy(stz.rels[i][1]);  # TODO necessary?
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
  Remove(stz.rels, index);
  expr := SEMIGROUPS.WordToExtRepObj(expr);
  Apply(stz.rels, x -> List(x, SEMIGROUPS.WordToExtRepObj));
  Apply(stz.rels, x -> List(x, y -> StzSubstitute(y, gen, expr)));
  Apply(stz.rels, x -> List(x, SEMIGROUPS.ExtRepObjToWord));

  # remove generator.
  # TODO this line is bad, doesn't actually do what we want
  # TCL: I will eventually change this so we're just storing strings in the
  # generators
  Remove(stz.gens, index);
end;
