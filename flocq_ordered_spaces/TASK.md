Read the .pdf file in the folder and generate three files: semimetrics.v, semimetrics.py and test.py

The file "semimetrics.v" should contain:
1. Formalization of ordered semimetric space as in .pdf but with the 
    output of distance d being rational numbers
    NOTE (Definition 9): the order law is the ANTITRIANGLE, not the
    ordinary triangle: for all a <= b <= c in the space,

        d(a,b) + d(b,c) <= d(a,c).

    (Do NOT formalize d(a,c) <= d(a,b) + d(b,c) -- that was a misreading
    of the paper that had to be redone. On the float example below the
    antitriangle holds with equality.)
2. Examples of ordered semimetric spaces on floating-point numbers 
    from Floc library:
        - The examples should use IEEE total order on reals that includes 
            NaN and other unusual floating point values
        - The distances should also handle non-numeric floating point
            values
        - Examples should include semimetric spaces similar to
            l_inf and l_1 norms if possible.
            * the l_1 vector space works with the plain pointwise order;
            * the l_infty vector space needs the SYNCHRONIZED-SHIFT
              order (pointwise order AND all component distances of
              the pair equal), because the plain pointwise order
              provably FAILS the antitriangle under max aggregation;
              keep the verified counterexample
              [1;1] <= [11;1] <= [11;8] with d_inf([1;1],[11;8]) = 10
              < 10 + 7 in the file;
            * lists of different lengths are INCOMPARABLE in the order;
              for the distance, pad the shorter list with the space
              point (NaN) and add a penalty equal to 1 whenever the
              lengths differ (needed for the identity of
              indiscernibles, e.g. d([nan],[nan,nan]) = 1).
        - The examples should be both on pure floats and on vectors of floats
        - Include one example where the antitriangle is necessarily a
          STRICT inequality: the squared distance
          d2(x,y) = (phi x - phi y)^2 on the SAME carrier and IEEE
          total order, with a proof that d2(a,b) + d2(b,c) < d2(a,c)
          for every chain a < b < c (e.g. d2(1,2) + d2(2,3) = 2 < 4 =
          d2(1,3)) and computed examples for NaN/inf/-0.

The file "semimetrics.py" should contain:
1. Python re-implementations of distance functions from
    example semimetric spaces in semimetrics.v
    (the phi-distance, the squared variant, and the l_1/l_infty
    vector distances with the NaN-padding and length-mismatch
    penalty, plus mirrors of the orders including the
    synchronized-shift order)

The file "test.py" should contain:
1. A differential testing between Rocq and Python implementations. Make sure distance
    results are exactly equal. 
2. Differential testing should be performed in two ways: first, a fixed test set should be
    generated that also includes special floating point values (both zeroes, NaNs, infinities)
    and second, there should be a random generator for floating point values that runs after
    the fixed dataset
3. Every ordered scalar pair should be tested under EVERY scalar
    distance (the plain and the squared one), and every vector case
    under both norms; expect ~1500 cases total and a runtime in the
    tens of minutes (squared extreme distances produce rationals
    with ~620-digit numerators)

As part of your process, leave a MEMORY.md with information you found important for the case the task
    has to be done from scratch again.
