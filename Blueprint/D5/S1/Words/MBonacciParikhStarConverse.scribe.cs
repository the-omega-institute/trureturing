using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciParikhStarConverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact all-start sentinel Parikh vectors and the full actual greedy converse.",
        H("The Uniform m-bonacci Parikh and Greedy Characterization"),
        Blocks(
            Paragraph(Text("The alphabet is Fin m. The original literal substitution phi sends a below m minus one to [0,a+1] and sends the terminal letter to [0]. word is the original unbounded limit of its nested iterates. boundary, factor, letterCount, parikhImage, T, U, S, fullGreedy and periodicDigits are reused at their original definitions. Every factor start is a natural q, including zero; k has no finite upper bound. S(k) is one plus the sum of the actual image lengths U(j) below k.")),
            Paragraph(Text("Let L_a(a)=[a] and L_a(b)=[a,b] otherwise. The actual phi is L_0 after rot on the same source letters. For a predecessor r and a length-|r|+1 source window v with the vector of r plus one excess letter b, write y=phi(v) and N=|phi(r)|+2. The true first source block determines the output offset delta, either zero or one. If rot(b)=0, y has length N-1; otherwise y has length N. At delta zero the singleton-excess window is y followed by zero and the two-letter-excess window is y. At delta one the two-letter-excess window is tail(y) followed by zero, while the singleton-excess window is tail(y) followed by zero and a next letter c. These are the four elementary windows; delta describes the first block, independently of the excess letter.")),
            Paragraph(Text("The next zero and its following output letter are supplied by the original right_extension_occurrence_iff on the actual source extension v followed by its next letter. If that following source image is a singleton, its following block supplies the second output letter. No image-length-two assumption is imposed. In the offset-one singleton-excess branch, c is the rotation of this next source letter and may differ from the previous excess letter. The proof keeps the same actual infinite word and boundary throughout.")),
            Paragraph(Text("Equal predecessor counts give an exact List.Perm between v and r followed by b. The pinned List permutation flatMap supplier transports it through phi, supplying both image length and counts. For a clipped initial zero, the private consumed clipping helper directly applies the pinned append permutation and cons cancellation suppliers to zero followed by t and y followed by zero. The other finite rearrangements use exact counts and additive cancellation. The proof uses neither a truncated-natural-subtraction identity nor cyclic conjugacy. The m=5 start-29 length-four factor 1001 obstructs a cyclic-conjugacy proxy, while the abelian statement remains the exact goal.")),
            Paragraph(Text("The Star property is used only for the induction predecessor. The empty predecessor is discharged by the actual one-letter factor at every start. Original boundary_window and the original strict/block laws locate each output q, including zero. Applying the four cases proves the successor Star upper inclusion. Original sentinel_frs, star_subset and star_injective then give every one of the m distinct vectors. A constant word illustrates why the upper inclusion by itself is insufficient.")),
            Paragraph(Text("The output is MSB-first and continues through U(0), keeping every trailing zero and the final partial period. k=0 gives n=1 and the list [1]. The proof covers k<m, k=m and k>m uniformly, and never uses rho(n)=m to infer a sentinel from periodic digits. Sentinel sufficiency holds already for m at least two. The integrated equivalences here retain m at least five; they do not claim the same full equivalence below five. No balance, finite sample completeness, cyclic conjugacy or alternative fixed word is a premise.")),
            Paragraph(Text("The sentinel converse is literature-attested in Ondrej Turek, Abelian complexity and Abelian co-decomposition, Theoretical Computer Science 469 (2013), pages 77\u201391, DOI 10.1016/j.tcs.2012.10.034, arXiv:1201.2109v1. The necessity is supplied by the existing source-bound formalization. The new work here is a Lean proof of the exact all-start transport and complete scanner inverse integrated with those original results; no mathematical novelty is claimed.")),
            Describe.Lean(
                DescribeId.Create("greedy-scan-injective"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciParikhStarConverse.greedyScan_injective"),
                H("A positive complete scan reconstructs its input"), StatementSource.FromAuthor(ConverseStatement("greedyScan_injective")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least two and every positive count, greedyScan(count) is injective on all natural remainders. At count one the quotient is the remainder because U(0) equals one. At a larger count, equal complete lists give equal leading quotients and equal remaining scans. Induction recovers equal remainders modulo the current weight; the exact quotient-plus-remainder identity recovers the input. No assumption on abelian complexity enters this direction. The count-zero scan is excluded because it is constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sentinel-parikh-image"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciParikhStarConverse.sentinel_parikh_image"),
                H("Exact all-start sentinel Parikh range"), StatementSource.FromAuthor(ConverseStatement("sentinel_parikh_image")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least two and every k, parikhImage(S(k)) equals the range of star(sentinelIter(k)). The upper inclusion is induction from the empty original sentinel. The lower inclusion uses the original fully right-special sentinel and star_subset. The original star_injective distinguishes every excess letter, so exactly m different vectors are attained. An upper Star inclusion alone does not imply attainment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-minimum-characterization"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciParikhStarConverse.uniform_minimum_characterization"),
                H("Uniform literal-word and complete-digit characterization"), StatementSource.FromAuthor(ConverseStatement("uniform_minimum_characterization")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least five and every n at least one, the complete all-start Parikh cardinality equals m if and only if n equals S(k) for some natural k, and if and only if the complete fullGreedy(n) list equals periodicDigits(k) for some natural k. Necessity is the direct original minimal_abelian_complexity_greedy result. Sentinel sufficiency uses the exact range theorem. Periodic digits imply the same sentinel count by the new positive scanner inverse: full output lengths identify a common top index, sentinel_top and scan_sentinel give the comparison list, and scanner injectivity recovers n. This is one endpoint with both transport and inverse on its live proof paths."))),
                DescribeRole.Theorem))));

    private static Formula ConverseStatement(string name)
    {
        var m = F.Id("m"); var n = F.Id("n"); var k = F.Id("k");
        var q = F.Id("q"); var i = F.Id("i"); var t = F.Id("t");
        var r = F.Id("r"); var s = F.Id("s"); var a = F.Id("a");
        var x = F.Id("x"); var count = F.Id("count");
        Formula ns = CFCall("S", m, k);
        Formula si = CFCall("sentinelIter", m, k);
        Formula rho = CFCall("ncard", CFCall("parikhImage", m, n));
        Formula minimum = CFEq(rho, m);
        Formula sentinel = CFEx("k", CFN(), CFEq(n, ns));
        Formula periodic = CFEx("k", CFN(), CFEq(CFCall("fullGreedy", m, n),
            CFCall("periodicDigits", m, k)));
        Formula body = name switch
        {
            "greedyScan_injective" => CFAll("count", CFN(),
                CFImp(CFLt(F.D(0), count), CFCall("Injective", CFCall("greedyScan", m, count)))),
            "sentinel_parikh_image" => CFAll("k", CFN(),
                CFEq(CFCall("parikhImage", m, ns), CFCall("range", CFCall("star", si)))),
            "uniform_minimum_characterization" => CFAll("n", CFN(),
                CFImp(CFLe(F.D(1), n), CFAnd(CFIff(minimum, sentinel), CFIff(minimum, periodic)))),
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        Formula bound = name == "uniform_minimum_characterization"
            ? CFAnd(CFLe(F.D(2), m), CFLe(F.D(5), m)) : CFLe(F.D(2), m);
        bool unrestricted = name is "star" or "star_injective" or "factor_add";
        return F.Disp(CFAll("m", CFN(), unrestricted ? body : CFImp(bound, body)));
    }

    private static Formula CFN() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula CFCall(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula CFAll(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEx(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CFLe(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CFLt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula CFAnd(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CFImp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula CFIff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
