## transformations.g: Semigroup Tietze Transformation Functions
##
## This file implements Tietze transformations 1-4 in
## a user-friendly format.

# TIETZE TRANSFORMATION 1: ADD REDUNDANT RELATION
TietzeTransformation1 := function(stz, pair)
  local s, free_fam, w1, w2, fp_fam, p1, p2;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <pair> should be a pair of LetterRep words.
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
