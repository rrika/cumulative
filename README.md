A [cumulative constraint](https://sofdem.github.io/gccat/gccat/Ccumulative.html) over tasks with
- an earliest start time
- a latest completion time
- a duration
- a resource demand

will restrict the time bounds so that concurrent tasks never go over a fixed resource capacity (C).

![](/cumulative.png)

One algorithm to implement it is [Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log n)][2].
This is (the work-in progress of) an implementation of this algorithm in Coq.
The files cumulative.py and cumulative_clean.py are (buggy?) prototypes I wrote before.

While it describes a different algorithm (I think?) [Max Energy Filtering Algorithm for Discrete
Cumulative Resources][1] by the same author makes understanding of the other paper easier.

(The graphic above is taken from [Simple and Scalable Time-Table Filtering for the Cumulative Constraint][3] which is -not- implemented here)

[1]: http://vilim.eu/petr/cpaior2009.pdf
[2]: http://vilim.eu/petr/cp2009.pdf
[3]: https://www.info.ucl.ac.be/~pschaus/assets/publi/cp2015_cumulative.pdf
