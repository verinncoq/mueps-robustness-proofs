Read the .pdf file in the folder and generate three files: semimetrics.v, semimetrics.py and test.py

The file "semimetrics.v" should contain:
1. Formalization of ordered semimetric space as in .pdf but with the 
    output of distance d being rational numbers
2. Examples of ordered semimetric spaces on floating-point numbers 
    from Floc library:
        - The examples should use IEEE total order on reals that includes 
            NaN and other unusual floating point values
        - The distances should also handle non-numeric floating point
            values
        - Examples should include semimetric spaces similar to
            l_inf and l_1 norms if possible.
        - The examples should be both on pure floats and on vectors of floats

The file "semimetrics.py" should contain:
1. Python re-implementations of distance functions from
    example semimetric spaces in semimetrics.v

The file "test.py" should contain:
1. A differential testing between Rocq and Python implementations. Make sure distance
    results are exactly equal. 
2. Differential testing should be performed in two ways: first, a fixed test set should be
    generated that also includes special floating point values (both zeroes, NaNs, infinities)
    and second, there should be a random generator for floating point values that runs after
    the fixed dataset

As part of your process, leave a MEMORY.md with information you found important for the case the task
    has to be done from scratch again.
