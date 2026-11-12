using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators.Approximation;

internal sealed class AccumulatedSupportRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/ekene2026accumulatedpsd");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite atomic probability on the actual unit ball gives ordinary accumulated best-term errors exceeding one.",
        H("Accumulated support approximation errors"),
        Blocks(
            Paragraph(Text("Write M for the uniform measure on the 64 unit-ball atoms A, Iota for the actual unit-ball coercion, S for the sum of the ambient atoms, C for their real linear combination, and E(d) for the original support-tuple squared-error set. F(d) is the matrix sparse error set with K=(I+J)/128 and x_i=1/8. SupportTuple(d) consists of all tuples in the actual support, including repeated entries, and RealTuple(d) is the unrestricted real coefficient space. Let t(d)=65(64-d)/(8192(d+1)), f(n)=inf E(n+1), and T be the sum of t(d) from d=1 to 63.")),
            Describe.Lean(DescribeId.Create("accumulated-support-barycenter-integrable"),
                DeclarationHandle.Create(Owner + "barycenter_integrable"), H("Integrability on the actual unit ball"),
                StatementSource.FromAuthor(Disp(Call("Integrable", V("Iota"), V("M")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("M is the measure (1/64) times the sum of the 64 Dirac measures at the unit atoms a_i=(e_0+e_i)/sqrt(2), on the actual closed unit-ball subtype of Euclidean 65-space. The coercion to that Euclidean space is Bochner integrable for M. Individual Dirac integrability, finite addition and finite scalar multiplication provide the proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-barycenter-eq"),
                DeclarationHandle.Create(Owner + "barycenter_eq"), H("The Bochner barycenter"),
                StatementSource.FromAuthor(Disp(Equal(Call("integral", V("Iota"), V("M")), Multiply(Frac(D(1), D(6,4)), V("S"))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual integral of the unit-ball coercion is (1/64) times the sum of all atoms. Finite-measure integrability is used to justify the finite-sum integral. No independently stipulated vector replaces the integral."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-support-eq"),
                DeclarationHandle.Create(Owner + "support_eq"), H("The actual topological support"),
                StatementSource.FromAuthor(Disp(Equal(Call("support", V("M")), Call("range", V("A"))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The topological support of M equals exactly the range of the unit-ball atoms. Each atom has positive mass in every neighborhood; the finite range is closed and its complement has zero mass. The barycenter and convex hull are not added to the dictionary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-error-bridge"),
                DeclarationHandle.Create(Owner + "error_bridge"), H("The Gram scaling"),
                StatementSource.FromAuthor(Disp(All("c", Call("RealTuple", D(6,4)), Equal(Call("error", V("c")), Call("quadratic", Call("subtract", V("x"), Multiply(D(8), V("c")))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real coefficient vector c on the 64 atoms, the squared Hilbert error of its combination equals (x-z)-transpose K(x-z), where z_i=8c_i. This equality uses the actual integral and actual Euclidean norm; the shared coordinate and the 64 independent coordinates give the two square terms."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-tuple-to-coefficients"),
                DeclarationHandle.Create(Owner + "tuple_to_coefficients"), H("Consolidation of repeated atoms"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"), All("a", Call("SupportTuple", V("d")), All("r", Call("RealTuple", V("d")), ExistsIn("c", Call("RealTuple", D(6,4)), And(Leq(Call("card", Call("support", V("c"))), V("d")), Equal(Call("tupleCombination", V("a"), V("r")), Call("C", V("c")))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural d, every d-tuple of actual support points, and every real d-tuple of coefficients, summing coefficients over equal atom indices yields a 64-coordinate vector of support cardinality at most d with the same approximant. Repetitions, negative coefficients and cancellations are allowed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-coefficients-to-tuple"),
                DeclarationHandle.Create(Owner + "coefficients_to_tuple"), H("Enumeration and zero padding"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"), All("c", Call("RealTuple", D(6,4)), Implies(Leq(Call("card", Call("support", V("c"))), V("d")), ExistsIn("a", Call("SupportTuple", V("d")), ExistsIn("r", Call("RealTuple", V("d")), Equal(Call("tupleCombination", V("a"), V("r")), Call("C", V("c")))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Conversely, every real coefficient vector with at most d nonzero coordinates is realized by a tuple of exactly d actual support points. Enumerate its nonzero support and pad the remaining slots by a fixed support point with coefficient zero. This also covers empty supports."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-error-set-eq"),
                DeclarationHandle.Create(Owner + "errorSet_eq"), H("Equality of the actual optimizing sets"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"), Equal(Call("E", V("d")), Call("F", V("d")))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural d, the original support-tuple squared-error set equals the full real sparse quadratic error set. Consolidation and enumeration give both directions, and multiplication by eight is invertible and preserves nonzero supports."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-errors-exact"),
                DeclarationHandle.Create(Owner + "errors_exact"), H("Attained Hilbert infima"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"), Implies(And(Leq(D(1), V("d")), Leq(V("d"), D(6,4))), Call("IsLeast", Call("E", V("d")), Call("t", V("d"))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every d between one and 64, the original support-tuple error set has least element t(d)=65(64-d)/(8192(d+1)). Equality of the actual sets transports the all-real lower bound and its attaining optimizer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-errors-zero"),
                DeclarationHandle.Create(Owner + "errors_zero"), H("The eventual zero errors"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"), Implies(Leq(D(6,4), V("d")), Call("IsLeast", Call("E", V("d")), D(0)))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every d at least 64, the actual error set has least element zero. All 64 atoms with coefficient 1/64 give the barycenter, and zero coefficients pad longer tuples. Squared norms are nonnegative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-ordinary-sum"),
                DeclarationHandle.Create(Owner + "ordinary_sum"), H("The ordinary infinite sum"),
                StatementSource.FromAuthor(Disp(Call("HasSum", V("f"), V("T")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The sequence of actual best squared errors at d=n+1 is zero for every n at least 63. It therefore HasSum T, where T is the finite sum of t(d) for d=1 through 63. This establishes ordinary convergence and uses no divergent-real-tsum fallback."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-support-refutation"),
                DeclarationHandle.Create(Owner + "result"), H("The full Hilbert assertion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("Q")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Q denotes the full original assertion: for every real Hilbert space H and probability measure on its unit ball, with v the Bochner barycenter, the squared infima of the errors over arbitrary real coefficients and exactly d points of the actual topological support, repetitions permitted, have an ordinary infinite sum at most one. The closed definition claim asserts existence of a real HasSum total with that bound, without assuming summability as an extra premise. The 64-atom witness has an integrable coercion, nonempty bounded-below error sets, attained infima and an eventual zero tail. Its ordinary total is T>1, so uniqueness of HasSum refutes Q. Ekene E., MathOverflow 509794 revision 2, CC BY-SA 4.0, supplies the original question. This is the second separately required negation in the same source event as the finite assertion."))), DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        a.Length == 0 ? V(s) : new Formula.Apply(V(s), [.. a]);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Close,Sp,Land,Sp,Open,b,Close);
    private static Formula Implies(Formula a, Formula b) => Seq(Open,a,Close,Sp,Rightarrow,Sp,b);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Open,V(s),Sp,Colon,Sp,t,Close,Comma,Sp,b);
    private static Formula ExistsIn(string s, Formula t, Formula b) => Seq(Exists,Sp,Open,V(s),Sp,Colon,Sp,t,Close,Comma,Sp,b);
}
