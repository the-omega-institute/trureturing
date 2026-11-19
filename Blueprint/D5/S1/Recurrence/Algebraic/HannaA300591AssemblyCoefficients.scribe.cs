using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300591AssemblyCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300591");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed ordered-block assemblies have exactly the ordinary exponential coefficients, " +
        "including an explicit finite unit-sign palette for every integer strict prefix.",
        H("The exponential coefficient formula for Hanna's assemblies"), Blocks(
            Describe.Lean(DescribeId.Create("hannaa300591-assembly-sum-coefficient"),
                DeclarationHandle.Create(Prefix + "assembly_sum_coefficient"),
                H("The full signed assembly formula"),
                StatementSource.FromAuthor(Disp(All("V", Call("FiniteTypes"),
                    All("C", Call("FiniteTypes"),
                    All("allowed", Call("Predicate", N(), V("C")),
                    All("S", Call("Finset", V("V")),
                    All("T", Call("Finset", V("V")),
                    All("sign", Call("Function", V("C"), Z()),
                        FormulaBody(Call("assemblySum", V("allowed"), V("S"), V("T"), V("sign")),
                            Call("colorSeries", V("allowed"), V("sign"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "V and C range over all finite types. The predicate allowed(j,c) and " +
                    "the integer weight sign(c) are arbitrary. An assembly is the existing " +
                    "finite set of disjoint nonempty ordered blocks covering S, with an " +
                    "allowed color on each block and two ordered ambient markers in T. " +
                    "The notation assemblySum is the integer sum of products of the color " +
                    "weights over all such assemblies; its cast to Q is displayed. " +
                    "The two markers can coincide and can lie outside the block or outside S. " +
                    "The size-j signed color sum is the sum of sign(c) over colors satisfying " +
                    "allowed(j,c). The series colorSeries has these ordinary coefficients " +
                    "for j>0 and constant coefficient zero.")),
                    Paragraph(Text(
                    "The proof uses the checked assembly_weight_point_recursion. For a " +
                    "chosen vertex x, it groups the actual root blocks by their support U. " +
                    "Their vertex orders have cardinality |U|!, their signed colors sum to " +
                    "the size-|U| color sum, and their independent markers contribute |T|^2. " +
                    "Erasing x identifies the possible root supports with subsets of S minus x. " +
                    "Mathlib's powerset-cardinality and permutation-cardinality identities " +
                    "give the binomial and factorial factors. Strong induction on |S| " +
                    "then identifies this exact recurrence with the derivative recurrence " +
                    "of the formal exponential, using DoldExponentialIntegrality.expSeries_derivative. " +
                    "The empty assembly supplies the constant term. This proves the identity " +
                    "in every degree without assuming any counting formula.")),
                    Paragraph(Text(
                    "The factorial multiplies an ordinary coefficient; the exponent contains " +
                    "the ordinary signed color coefficients, without factorial rescaling. " +
                    "The vertex support shrinks in the induction and the marker domain T " +
                    "stays unchanged. In particular, a pointed assembly on S minus a vertex " +
                    "can retain all of S as its marker set.")),
                    Paragraph(Text(
                    "Combining this identity with fixed_assembly_weight_factorization " +
                    "also evaluates the existing FixedAssembly sum. Write F for the vertices " +
                    "of S fixed by g, W for the vertices of T fixed by g, and M for the signed " +
                    "sum of invariant assemblies on the moved vertices with markers in T. " +
                    "The rational cast of the fixed-assembly sum is exactly " +
                    "M times |F|! times [x^|F|]exp(|W|^2 P), where P is colorSeries. " +
                    "The same application for the explicit prefix palette replaces P by " +
                    "prefixSeries. FixedAssembly here is the existing stability predicate " +
                    "under simultaneous vertex and marker relabeling. The actual group-action " +
                    "and fixedBy equivalences are proved by this module's internal action lemmas."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hannaa300591-signed-prefix-assembly-coefficient"),
                DeclarationHandle.Create(Prefix + "signed_prefix_assembly_coefficient"),
                H("An actual finite signed palette for every integer prefix"),
                StatementSource.FromAuthor(Disp(All("V", Call("FiniteTypes"),
                    All("N", N(), All("a", Call("Function", N(), Z()),
                    All("S", Call("Finset", V("V")),
                    All("T", Call("Finset", V("V")),
                        Seq(Call("unitSigns", V("N"), V("a")), Sp, Land, Sp,
                            FormulaBody(Call("prefixAssemblySum", V("N"), V("a"), V("S"), V("T")),
                                Call("prefixSeries", V("N"), V("a"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any natural N and any integer sequence a, PrefixColor is the " +
                    "finite dependent union, over j<N, of Fin(max(a(j),0)) and " +
                    "Fin(max(-a(j),0)). The first component has sign +1, the second sign -1, " +
                    "and a color can decorate precisely a block of its own size j. " +
                    "The unitSigns clause states that every color has one of these two signs. " +
                    "The signed color sum at j is a(j) for j<N and zero otherwise, " +
                    "by the exact positive-minus-negative integer identity. Empty color " +
                    "fibers and negative entries require no additional hypothesis. " +
                    "The series prefixSeries has coefficient a(j) for 0<j<N and zero " +
                    "otherwise. Colors at zero never decorate a nonempty block.")),
                    Paragraph(Text(
                    "The prefixAssemblySum uses precisely this finite palette and its " +
                    "unit signs in the existing Assembly type. The theorem proves both " +
                    "the unit-sign property and the displayed coefficient identity, for " +
                    "every S and T, including empty sets and degrees beyond N. " +
                    "For the A300591 induction, N is the current index and a is the " +
                    "actual integral strict prefix. This theorem supplies a counting " +
                    "realization of that prefix, and assumes no integrality of the next " +
                    "coefficient or of an exponential coefficient.")),
                    Paragraph(Text(
                    "The rational source and companion identifications remain those of " +
                    "HannaA300591RationalModel: A300591 uses ordinary coefficients, " +
                    "A300590 uses the entries r! times the ordinary coefficients of exp(A), " +
                    "and A300598 denotes a(n)/n only for n>=1. The residual integrality " +
                    "theorems below supply the coprime-prime step used by the source induction."))),
                DescribeRole.Theorem),
            ResultNode("signed_prefix_residual_local_integral", "The integral strict-prefix arithmetic step",
                ResidualStatement(),
                "For every N>=1, arbitrary integer sequence a, prime p not dividing N, " +
                "and P=prefixSeries(N,a), assume the actual equations with P for every " +
                "1<=f<N. Then [x^N]exp(N^2 P)-N^2[x^(N-1)]exp(N^2 P) has denominator " +
                "coprime to p. The explicit unit-signed finite palette is used on Fin N. " +
                "FullAssembly and PointedAssembly carry simultaneous permutation actions; " +
                "the latter retains marker domain V after removing its distinguished point. " +
                "Their weights are invariant. FixedBy corresponds to structural stability, " +
                "and the fixed pointed objects have three fixed-vertex choices. With f fixed " +
                "vertices and moved weight sum M, subtraction is M f! times the degree-f " +
                "residual. Positive and negative invariant fibers give signed Burnside by " +
                "Mathlib ordinary Burnside. A Sylow p-subgroup has order p^v_p(N!), and " +
                "every element fixes a vertex when p does not divide N, by the p-group " +
                "fixed-point theorem for its cyclic subgroup. Nonidentity elements fix " +
                "fewer than N vertices, so their lower residuals vanish. At the identity " +
                "the moved part is uniquely empty. The full p-power in N! divides the " +
                "integer signed subtraction; padicValInt_dvd_iff and padicValRat.mul " +
                "cancel its valuation exactly, with zero handled separately. " +
                "No positivity, next-coefficient integrality, action fact, orbit identity, " +
                "Sylow order or factorial cancellation is an unproved premise."))));

    private static Formula ResidualStatement()
    {
        var prefix = Call("prefixSeries", V("N"), V("a"));
        Formula Scalar(Formula n) => new Formula.Power(Call("castQ", n), D(2));
        Formula E(Formula n) => Call("exp", Mul(Scalar(n), prefix));
        Formula Previous(Formula n) =>
            Call("coeff", Sub(n, D(1)), E(n));
        Formula Equation(Formula n) =>
            Eqn(Call("coeff", n, E(n)), Mul(Scalar(n), Previous(n)));
        var lower = All("f", N(), Imp(Leq(D(1), V("f")),
            Imp(Lt(V("f"), V("N")), Equation(V("f")))));
        var residual = Sub(Call("coeff", V("N"), E(V("N"))),
            Mul(Scalar(V("N")), Previous(V("N"))));
        var conclusion = Imp(lower, Call("IsRIntegralRat", V("p"), residual));
        var primes = All("p", N(), Imp(Call("Prime", V("p")),
            Imp(Seq(Neg, Sp, Call("Dvd", V("p"), V("N"))), conclusion)));
        return All("N", N(), All("a", Call("Function", N(), Z()),
            Imp(Leq(D(1), V("N")), primes)));
    }

    private static DocumentBlock ResultNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("hannaa300591-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula FormulaBody(Formula total, Formula exponent) =>
        Eqn(Call("castQ", total), Mul(Call("factorial", Call("card", V("S"))),
            Call("coeff", Call("card", V("S")),
                Call("exp", Mul(Call("square", Call("card", V("T"))), exponent)))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
}
