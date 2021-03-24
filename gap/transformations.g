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
