using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PhysicalGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual fixed-isometry residuals have a full occupation Gram formula and a physical memory lower bound.",
        H("Physical Gram Necessity"),
        Blocks(
            Paragraph(Text(
                "The alphabet sigma is finite and nonempty. Capacities a(i) are arbitrary natural " +
                "numbers. H is an arbitrary finite-dimensional complex inner-product space. " +
                "Box(a) consists of occupations r with r(i) in Fin(a(i)+1); |r| is the sum of their " +
                "values and M(r)=|r|!/product(i,r(i)!). All square roots below are nonnegative real " +
                "square roots, included in Complex. FixedIsometry(H,sigma) denotes a total complex " +
                "linear isometry from H to EuclideanSpace(Complex,sigma) tensor H.")),
            Theorem("residual-word-formula", "residual_word_formula", "Evolution along every admissible horizon",
                All("V", Isometry, All("phi", VectorFamily,
                    Seq(Call("Step", a, v, phi), Sp, Implies, Esc,
                        Call("ResidualEvolution", a, v, phi)))),
                "Assume the one-letter Step law for the same V, guarded by r nonzero. For every " +
                "r and every word w with length at most |r|, wordOp(V,w,phi(r)) equals " +
                "sqrt(M(r-counts(w))/M(r)) times phi(r-counts(w)) if every letter count is at " +
                "most r(i), and zero otherwise. Subtraction is coordinatewise natural subtraction. " +
                "Induction on w uses the multinomial erasure recurrence to telescope the legal " +
                "coefficients; the first illegal letter and the illegal-tail case both give zero. " +
                "The empty word is included, without imposing a transition at r=0."),
            Theorem("stationary-normalized-gram", "stationary_normalized_gram", "The complete residual Gram data",
                All("V", Isometry, All("f", memory, All("phi", VectorFamily,
                    Seq(Grp(All("r", box, Seq(Call("norm", Call("phi", r)), Sp, Eq, Sp, D(1)))),
                        Sp, Land, Sp, Call("phi", D(0)), Sp, Eq, Sp, F.Id("f"),
                        Sp, Land, Sp, Call("Step", a, v, phi), Sp, Implies, Esc,
                        Call("NormalizedGram", a, F.Id("f"), phi))))),
                "Let G(r,s)=inner(phi(r),phi(s)) and z(d)=inner(phi(d),f), with unit phi and " +
                "phi(0)=f. When s<=r coordinatewise, G(r,s)=sqrt(M(s)M(r-s)/M(r)) z(r-s). " +
                "When r<=s, the reverse formula is sqrt(M(r)M(s-r)/M(s)) conjugate(z(s-r)). " +
                "Incomparable indices have zero inner product. To compute the first formula, " +
                "continue both vectors for the shorter horizon |s|. The word law leaves exactly " +
                "the M(s) words of occupation s; their equal contributions have coefficient " +
                "sqrt(M(r-s)/M(r)) sqrt(1/M(s)). Summation gives the stated coefficient and " +
                "retains the phase in z. Conjugate symmetry handles the opposite order of horizons.",
                "The same conclusion gives G Hermitian and positive semidefinite, G(r,r)=1, " +
                "z(0)=1, and rank G<=finrank(Complex,H). Define D(r,r)=sqrt(M(r)), " +
                "Dinv(r,r)=1/sqrt(M(r)), and B=DGD. Positivity of M(r) gives both inverse " +
                "identities. B is exactly the Gram matrix of sqrt(M(r)) times phi(r), is positive " +
                "semidefinite, has B(0,0)=1, and has the same rank as G.",
                "For nonzero r and nonzero s, inner-product preservation by the same V gives " +
                "B(r,s)=sum(i,B(r-e(i),s-e(i))), retaining a summand only when both r(i) and " +
                "s(i) are positive. The scaled Step coefficient follows from " +
                "|r| M(r-e(i))=r(i)M(r). The stationary Gram rank theorem applied to this " +
                "actual B gives rank G>=product(i,a(i)+1)-max(i,a(i)), with natural subtraction. " +
                "Its conditional-kernel, polynomial-coordinate, rigidity and nullity arguments " +
                "remain in that reused theorem. No recurrence at a zero residual is required.",
                "For all-zero capacities, Box(a) has one element, G is the identity, rank G=1, " +
                "and finrank(Complex,H)>=1. This is a boundary clause of the universal result."),
            Theorem("physical-gram-from-exact-preparation", "physical_gram_from_exact_preparation",
                "The actual preparation and its dimension bound", Endpoint(),
                "Given a PhysicalPreparation P, set phi=residual(a,P.V,P.initial). The result " +
                "returns four fields: the actual NormalizedResiduals including all prefix " +
                "equalities, universal ResidualEvolution, the full NormalizedGram, and " +
                "product(i,a(i)+1)-max(i,a(i))<=finrank(Complex,H). The Gram calculation uses " +
                "the Step and phase data extracted from P, so its vectors belong to the actual " +
                "physical memory. Neither residual equations nor Gram equations are added as " +
                "hypotheses on P.",
                "For (4,2,1,1), the stationary lower bound is (5*3*2*2)-4=56. The corresponding " +
                "exact target has 840 words of amplitude 1/sqrt(840). Attainment is a separate " +
                "construction; the time-dependent minimum 12 concerns a different control model."))));

    private static readonly Formula sigma = F.Id("sigma"), memory = F.Id("H"), a = F.Id("a");
    private static readonly Formula v = F.Id("V"), phi = F.Id("phi"), r = F.Id("r");
    private static Formula box => Call("Box", a);
    private static Formula Isometry => Call("FixedIsometry", memory, sigma);
    private static Formula VectorFamily => Seq(box, Sp, To, Sp, memory);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Esc, body);

    private static Formula Domain(Formula body) => Disp(Seq(
        Forall, Sp, sigma, Colon, Sp, F.Id("Type"), Comma, Sp,
        Call("Fintype", sigma), Comma, Sp, Call("DecidableEq", sigma), Comma, Sp,
        Call("Nonempty", sigma), Comma, Esc,
        Forall, Sp, memory, Colon, Sp, F.Id("Type"), Comma, Sp,
        Call("NormedAddCommGroup", memory), Comma, Sp,
        Call("InnerProductSpace", F.Id("Complex"), memory), Comma, Sp,
        Call("FiniteDimensional", F.Id("Complex"), memory), Comma, Esc,
        Forall, Sp, a, Colon, Sp, sigma, Sp, To, Sp, F.Id("Nat"), Comma, Esc, body));

    private static DocumentBlock Theorem(string id, string declaration, string title,
        Formula statement, params string[] paragraphs) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/StationaryPreparation/PhysicalGram." + declaration),
            H(title), StatementSource.FromAuthor(Domain(statement)), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(text => Paragraph(Text(text))).ToArray()), DescribeRole.Theorem);

    private static Formula Endpoint()
    {
        Formula p = F.Id("P"), pv = Call("V", p), initial = Call("initial", p), final = Call("final", p);
        Formula actual = Call("residual", a, pv, initial), i = F.Id("i");
        Formula size = Seq(Prod, Underscore, Grp(Seq(i, Sp, InMacro, Sp, sigma)), Sp,
            Open, Call("a", i), Sp, Plus, Sp, D(1), Close);
        Formula lower = Call("NatSub", size, Call("FinsetSup", Call("univ", sigma), a));
        return All("P", Call("PhysicalPreparation", a, memory), Seq(
            Call("NormalizedResiduals", a, pv, initial, final, actual), Sp, Land, Esc,
            Call("ResidualEvolution", a, pv, actual), Sp, Land, Esc,
            Call("NormalizedGram", a, final, actual), Sp, Land, Esc,
            lower, Sp, Leq, Sp, Call("finrank", F.Id("Complex"), memory)));
    }
}
