using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class HoggarSicSumNegativityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/HoggarSicSumNegativity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/debrota2017negativity");

    private const string SourceQuotation = """
        Although dimension $5$ was the last in which we were able to explicitly calculate the sum negativity for the SIC Q-reps by exhaustive combinatorial searching, we suspect that we have found the correct sum negativity for $\{Q_j^-\}$ constructed with the Hoggar SIC in dimension $8$. Rather than calculating the eigenvalues of every partial sum matrix (since this is infeasible for $2^{64}$, $8\times8$ matrices), we used a numerical local maximization procedure and around $10^6$ random pure state seeds. The overall maximum value we found, $7/8$, occurred frequently in our data and is significantly larger than all of the smaller local maxima. Of course, we could still be falling short of the global maximum value if it occurs at very hard to access positions. The states whose quasiprobability representations achieve the sum negativity of $7/8$ consist of $28$ copies of value $-1/32$ and $36$ copies of value $5/96$.
        """;
    private const string NegativePartQuotation = """
        which replaces the positive elements of $\mathfrak{p}$ with zero and the negative elements with their absolute value.
        """;
    private const string SumNegativityQuotation = """
        We will refer to the special cases $N^1$ and $N^\infty$, which we see are equivalent to the two natural candidates proposed above, as the sum negativity and the ceiling negativity respectively.
        """;

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum negativity of the Hoggar-SIC Q-minus representation in dimension eight has global maximum 7/8 over all density matrices.",
        H("The sharp Hoggar-SIC sum negativity"),
        Blocks(
            Node("vector", "The three-qubit Pauli orbit", VectorFormula(),
                "The Hoggar fiducial is v = (-1+2i, 1, 1, 1, 1, 1, 1, 1). "
                + "Stacey, arXiv:1609.03075, equation (26), writes this vector and generates its orbit by three qubit Weyl-Heisenberg factors. "
                + "Here j = 8x + z, with x and z the integers 0 through 7 representing their three low binary bits; b also runs from 0 through 7. "
                + "The private Gaussian-integer expression orbitG(j,b) is bitSign(z, xor(b,x)) times (-1+2i if b=x, otherwise 1). "
                + "The sign bitSign(z,a) is 1 if the sum of the three products of the corresponding binary bits is even, and -1 otherwise. "
                + "In the displayed formula val maps Fin to Nat, div is Nat.div, mod is Nat remainder, xor is Nat.xor, and ite selects its branches. "
                + "Zsqrtd.mk(-1,2) is the Gaussian integer with real part -1 and imaginary part 2. "
                + "Thus the coefficient at b is (-1)^(z dot (b+x)) v_(b+x), exactly the action D_(x,z)|a> = (-1)^(z dot a)|a+x>; addition of bit vectors is xor. "
                + "GaussianInt.toComplex is the canonical map from the Gaussian integers to C.",
                "hoggarVector", AssessedProvenance.FromLiterature(Source)),
            Node("projector", "The normalized Hoggar projectors", ProjectorFormula(),
                "Each orbit vector has squared norm 12. The projector is the outer product of that vector with its conjugate, scaled by 1/12. "
                + "vecMulVec(f,g) has entry (a,b) equal to f(a)g(b); star on a vector is pointwise complex conjugation. "
                + "Scalars in this formula are complex. Distinct projectors have trace overlap 1/9.",
                "hoggarProjector", AssessedProvenance.FromLiterature(Source)),
            Node("qrep", "The paper's Q-minus representation", QFormula(),
                "DeBrota and Fuchs, arXiv:1703.08272v2, equation (12), define Q_j^plus/minus = minus/plus sqrt(d+1) Pi_j + (1/d)(1 plus/minus sqrt(d+1)) I. "
                + "For the minus choice and d=8 this is 3 Pi_j - I/4. Here the scalars are complex and I is the 8 by 8 identity matrix.",
                "hoggarQ", AssessedProvenance.FromLiterature(Source)),
            Node("quasiprobability", "The real quasiprobability coordinates", QuasiprobabilityFormula(),
                "The paper's definition of a quasiprobability representation and equation (10) use q(j) = Tr(rho F_j) with F_j = Q_j/8. "
                + "The definition explicitly takes the real part. For density matrices the trace is real because rho and Q_j are Hermitian; this is used in the proof of Parseval. "
                + "The division by 8 is real division and introduces no extra dimension factor into negativity.",
                "quasiprobability", AssessedProvenance.FromLiterature(Source)),
            Node("negativepart", "The negative part", NegativePartFormula(),
                "Equation (8), page 7, defines the negative part as (|p(j)|-p(j))/2, "
                + "\"" + NegativePartQuotation + "\" "
                + "Here p is one real coordinate, so negativePart(p) is this scalar expression. The proof establishes its equality to max(0,-p).",
                "negativePart", AssessedProvenance.FromLiterature(Source)),
            Node("negativity", "Sum negativity of a density matrix", NegativityFormula(),
                "Page 7: \"" + SumNegativityQuotation + "\" "
                + "Equations (9) and (10) define N^p as the L^p norm of the negative part. "
                + "For p=1 the nonnegative negative-part coordinates sum to the displayed expression, over each of the 64 indices exactly once.",
                "sumNegativity", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured global maximum", ClaimFormula(),
                "DeBrota and Fuchs, arXiv:1703.08272v2, Section 6, page 17: \"" + SourceQuotation + "\" "
                + "Equation (11) takes the maximum over quantum state space. The encoding uses every complex 8 by 8 positive-semidefinite matrix rho with complex trace equal to 1, including mixed states. "
                + "IsGreatest asserts both membership of 7/8 in the displayed set and the upper bound for every member; r is real.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("hoggar-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The maximum is seven eighths"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The Gaussian-integer orbit certificate gives all 4096 squared overlaps: 144 on the diagonal and 16 off it. "
                    + "The 64 Q matrices are trace-orthogonal with trace(Q_j Q_k)=8 delta_(j,k), so they form a basis of the 64-dimensional complex matrix space. "
                    + "Recovering the expansion coefficients gives sum_j q(j)^2 = Tr(rho^2)/8, while sum_j q(j)=1 and q(j)>=-1/32. "
                    + "Nonnegative eigenvalues and trace one imply Tr(rho^2)<=1. The quadratic majorant (9/2)(t-5/96)^2 bounds max(0,-t) for t>=-1/32; summing gives N<=7/8. "
                    + "For w=conj(v), the state w w*/12 has 28 coordinates -1/32 and 36 coordinates 5/96, giving N=7/8. "
                    + "The conclusion includes every mixed density matrix, not just the pure attaining state."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debrota-2017-hoggar-sic-sum-negativity"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hoggar-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(SourceParagraph(prose)), DescribeRole.Definition);

    private static DocumentBlock SourceParagraph(string prose)
    {
        string[] spans = prose.Split('$');
        List<Inline> content = [];
        for (int index = 0; index < spans.Length; index++)
        {
            if (spans[index].Length == 0) continue;
            if (index % 2 == 0) content.Add(Text(spans[index]));
            else if (spans[index] == @"\mathfrak{p}") content.Add(Text("𝔭"));
            else content.Add(Math(QuotationMath(spans[index])));
        }
        return Paragraph([.. content]);
    }

    private static Formula QuotationMath(string span) => span switch
    {
        "5" => D(5),
        "8" => D(8),
        "28" => D(2, 8),
        "36" => D(3, 6),
        @"\{Q_j^-\}" => Seq(OpenBrace,
            F.Id("Q"), Underscore, Grp(F.Id("j")), Caret, Grp(Minus), CloseBrace),
        "2^{64}" => new Formula.Power(D(2), D(6, 4)),
        @"8\times8" => Seq(D(8), Sp, Times, Sp, D(8)),
        "10^6" => new Formula.Power(D(1, 0), D(6)),
        "7/8" => Seq(D(7), Slash, D(8)),
        "-1/32" => Seq(Minus, D(1), Slash, D(3, 2)),
        "5/96" => Seq(D(5), Slash, D(9, 6)),
        "N^1" => new Formula.Power(F.Id("N"), D(1)),
        @"N^\infty" => new Formula.Power(F.Id("N"), Infty),
        _ => throw new ArgumentException("Unsupported mathematics in the source quotation.", nameof(span))
    };

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Matrices => Call("Matrix", Call("Fin", D(8)), Call("Fin", D(8)), Complexes);
    private static Formula Fin64 => Call("Fin", D(6, 4));
    private static Formula Half(Formula p) => new Formula.Fraction(
        Parenthesized(new Formula.Binary(new Formula.Absolute(p), FormulaBinaryOperator.Subtract, p)), D(2));

    private static Formula VectorFormula()
    {
        Formula j = F.Id("j"), b = F.Id("b");
        Formula jVal = Call("val", j), bVal = Call("val", b);
        Formula x = Call("div", jVal, D(8));
        Formula z = new Formula.Modulo(jVal, D(8));
        Formula a = Call("xor", bVal, x);
        Formula LowBit(Formula t) => new Formula.Modulo(t, D(2));
        Formula Bit(Formula t, Formula divisor) => LowBit(Call("div", t, divisor));
        Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
        Formula dot = Add(Add(Mul(LowBit(z), LowBit(a)), Mul(Bit(z, D(2)), Bit(a, D(2)))), Mul(Bit(z, D(4)), Bit(a, D(4))));
        Formula sign = Call("ite", Parenthesized(Equal(new Formula.Modulo(dot, D(2)), D(0))), D(1), new Formula.Negate(D(1)));
        Formula gaussianEntry = new Formula.Apply(
            Seq(Operatorname, Grp(Seq(F.Id("Zsqrtd"), Dot, F.Id("mk")))),
            [new Formula.Negate(D(1)), D(2)]);
        Formula entry = Call("ite", Parenthesized(Equal(bVal, x)), gaussianEntry, D(1));
        Formula rhs = Call("toComplex", Mul(Parenthesized(sign), Parenthesized(entry)));
        return Disp(All(j, Fin64, All(b, Call("Fin", D(8)),
            Equal(Call("hoggarVector", j, b), rhs))));
    }
    private static Formula ProjectorFormula()
    {
        Formula j = F.Id("j"), u = Call("hoggarVector", j);
        return Disp(All(j, Fin64, Equal(Call("hoggarProjector", j),
            Mul(new Formula.Fraction(D(1), D(1, 2)), Call("vecMulVec", u, Call("star", u))))));
    }
    private static Formula QFormula()
    {
        Formula j = F.Id("j");
        return Disp(All(j, Fin64, Equal(Call("hoggarQ", j),
            new Formula.Binary(Mul(D(3), Call("hoggarProjector", j)), FormulaBinaryOperator.Subtract,
                Mul(new Formula.Fraction(D(1), D(4)), F.Id("I"))))));
    }
    private static Formula QuasiprobabilityFormula()
    {
        Formula rho = Rho, j = F.Id("j");
        return Disp(All(rho, Matrices, All(j, Fin64,
            Equal(Call("quasiprobability", rho, j), new Formula.Fraction(
                Call("Re", Call("Tr", Mul(rho, Call("hoggarQ", j)))), D(8))))));
    }
    private static Formula NegativePartFormula()
    {
        Formula p = F.Id("p");
        return Disp(All(p, Reals, Equal(Call("negativePart", p), Half(p))));
    }
    private static Formula NegativityFormula()
    {
        Formula rho = Rho, j = F.Id("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, Colon, Sp, Fin64)), Sp,
            Call("negativePart", Call("quasiprobability", rho, j)));
        return Disp(All(rho, Matrices, Equal(Call("sumNegativity", rho), sum)));
    }
    private static Formula ClaimFormula()
    {
        Formula rho = Rho, r = F.Id("r");
        Formula conditions = And(Call("PosSemidef", rho),
            And(Equal(Call("Tr", rho), D(1)), Equal(Call("sumNegativity", rho), r)));
        Formula exists = Seq(Exists, Sp, rho, Sp, Colon, Sp, Matrices, Comma, Sp, conditions);
        Formula set = Seq(OpenBrace, r, Sp, Colon, Sp, Reals, Sp, Mid, Sp, exists, CloseBrace);
        return Disp(Iff(F.Id("claim"), Call("IsGreatest", set, new Formula.Fraction(D(7), D(8)))));
    }
}
