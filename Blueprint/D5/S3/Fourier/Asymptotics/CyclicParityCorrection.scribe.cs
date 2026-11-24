using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicParityCorrectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicParityCorrection";

    private static readonly Formula Q = F.Id("q");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula W = F.Id("w");
    private static readonly Formula Hscale = F.Id("H");
    private static readonly Formula Z = F.Id("Z");
    private static readonly Formula A = F.Id("A");
    private static readonly Formula Threshold = F.Id("a");
    private static readonly Formula C = F.Id("C");
    private static readonly Formula Beta = F.Id("beta");
    private static readonly Formula Rho = F.Id("rho");
    private static readonly Formula Delta = F.Id("delta");
    private static readonly Formula Mu = F.Id("mu");
    private static readonly Formula Neighbor = F.Id("s");
    private static readonly Formula Zero = F.D(0);
    private static readonly Formula One = F.D(1);
    private static readonly Formula Two = F.D(2);
    private static readonly Formula Naturals = F.Id("Nat");
    private static readonly Formula Reals = F.Id("Real");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The attained minimum sampled cosine gives an exact root of the finite dual certificate.",
        H("Antipodal certificate for two cosine constraints"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-angular-mesh"),
                DeclarationHandle.Create(Owner + ".mesh"), H("Angular spacing"),
                StatementSource.FromAuthor(F.Disp(All("q", Naturals,
                    Eq(Call("h", Q), Div(Multiply(Two, F.Pi), Q))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For positive modulus q, the mesh is the angular difference between adjacent residues."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("centered-cosine-sample"),
                DeclarationHandle.Create(Owner + ".sample"), H("Centered cosine sample"),
                StatementSource.FromAuthor(F.Disp(All("q", Naturals, All("i", Call("ZMod", Q),
                    Eq(Call("c", I), Call("cos", Call("CenteredAngle", I))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The centered angle uses the integer representative in the half-open centered interval."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("antipodal-dual-certificate"),
                DeclarationHandle.Create(Owner + ".antipodal_dual_certificate"),
                H("The two roots and the energy identity"),
                StatementSource.FromAuthor(DualStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive q, let h=2π/q, d=(q mod 2)/2 and C=−cos(dh). " +
                        "The centered representative floor(q/2) attains C. Every centered representative " +
                        "has absolute value at most floor(q/2), so the cosine is at least C.")),
                    Paragraph(Text(
                        "For H,Z>0 and C<1, set β=(t−H(1−C²))/(1−C), ρ=−C−β/H and " +
                        "p(i)=(t−H(1−c(i)²)−β(1−c(i)))/Z. Write p₊ for the positive part. " +
                        "The factorization holds even when the two roots coincide. A sample at C has p₊=0.")),
                    Paragraph(Text(
                        "The energy identity applies to every feasible v at threshold a. B is the dual bound " +
                        "2(t−(H/2+β)(1−a))/Z−Σ p₊², R is Σ(v−p₊)², and J is Σv(p₊−p). " +
                        "The two moment slacks are M₁(v)−a and M₂(v)−a. The identity gives E(v)≥B when β≥0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-antipodal-mass-transfer"),
                DeclarationHandle.Create(Owner + ".adjusted"), H("Mass transfer"),
                StatementSource.FromAuthor(TransferStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The indicator at each listed residue acts on the corresponding scalar increment. " +
                    "The closest antipodal residue chosen here has centered representative floor(q/2) for q>0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-two-deficit-comparison"),
                DeclarationHandle.Create(Owner + ".adjusted_matches_moments"),
                H("Exact matching of the two deficits"),
                StatementSource.FromAuthor(PrimalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q>4 and let w be nonnegative with mass one. Define Dᵣ=1−Mᵣ(w), F=1−cos(h), " +
                        "G=1−cos(2h), U=1−C and V=2(1−C²). For target deficit A, take " +
                        "δ=(A−D₂−V(A−D₁)/U)/(G−VF/U) and μ=(A−D₁−Fδ)/U. Both denominators must be nonzero.")),
                    Paragraph(Text(
                        "Assume w(0)−δ−μ≥0, w(1)+δ/2≥0, w(−1)+δ/2≥0 and μ≥0. " +
                        "The transfer gives a feasible v at threshold 1−A, with equality in both moments. " +
                        "The moment increments in deficit coordinates are Fδ+Uμ and Gδ+Vμ. " +
                        "Both equations follow by substitution, and the four increments sum to zero."))),
                DescribeRole.Theorem))));

    private static Formula DualStatement()
    {
        var c = Call("c", I);
        var p = Call("p", I);
        var positivePart = Call("PositivePart", p);
        var roots = All("i", Call("ZMod", Q), And(Le(C, c),
            And(Eq(p, Div(Multiply(Multiply(Hscale, Subtract(c, C)), Subtract(c, Rho)), Z)),
                new Formula.Logic(Lt(Zero, positivePart), FormulaLogicOperator.Iff,
                    And(Lt(C, c), Lt(Rho, c))))));
        var energy = Eq(Call("E", V),
            Add(Add(Add(Add(Call("B", Threshold), Call("R", V)), Multiply(Two, Call("J", V))),
                    Multiply(Div(Multiply(Two, Beta), Z), Subtract(Call("M", One, V), Threshold))),
                Multiply(Div(Hscale, Z), Subtract(Call("M", Two, V), Threshold))));
        return F.Disp(And(roots, All("v", Call("Feasible", Q, Threshold), energy)));
    }

    private static Formula TransferStatement()
    {
        var residues = Call("ZMod", Q);
        var rhs = Add(Add(Add(Subtract(Call("w", I), Multiply(Add(Delta, Mu), Call("Indicator", Zero, I))),
                    Multiply(Neighbor, Call("Indicator", One, I))),
                Multiply(Neighbor, Call("Indicator", F.Seq(F.Neg, F.Sp, One), I))),
            Multiply(Mu, Call("Indicator", Call("HalfFloor", Q), I)));
        return F.Disp(All("q", Naturals, All("w", Call("Weights", Q),
            All("delta", Reals, All("mu", Reals, All("s", Reals, All("i", residues,
                Eq(Call("Adjusted", W, Delta, Mu, Neighbor, I), rhs))))))));
    }

    private static Formula PrimalStatement()
    {
        var threshold = Subtract(One, A);
        var v = Call("Adjusted", W, Delta, Mu, Div(Delta, Two));
        return F.Disp(And(Call("Feasible", Q, threshold, v),
            And(Eq(Call("M", One, v), threshold), Eq(Call("M", Two, v), threshold))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
}
