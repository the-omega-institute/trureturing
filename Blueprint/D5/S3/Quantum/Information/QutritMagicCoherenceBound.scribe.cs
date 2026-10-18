using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class QutritMagicCoherenceBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/QutritMagicCoherenceBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mukhopadhyay2018coherencemagic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every normalized pure qutrit state, the sum negativity is at least (C/2) sqrt(1 - C/2), where C is its l1 coherence.",
        H("A lower bound on qutrit magic from coherence"), Blocks(
            Paragraph(Text(
                "Use the computational basis with indices 0, 1 and 2. Fin(3) is this index set. "
                    + "The rows and columns of every displayed array are ordered 0, 1, 2. "
                    + "Complex absolute values denote moduli, and Re and Im denote real and imaginary parts.")),
            Node("wigner", "The nine Wigner entries", WignerFormula(),
                "The array defines wigner for every complex 3 by 3 matrix, using the real parts "
                    + "of its diagonal entries. For density matrices it is the discrete Wigner "
                    + "function of Eq. (12), with both phase-space indices shifted from 1, 2, 3 "
                    + "to 0, 1, 2. In particular, the imaginary part of the 02 entry has the "
                    + "opposite sign pattern to those of the 01 and 12 entries."),
            Node("sumNegativity", "The sum negativity", NegativityFormula(),
                "The sum negativity is the sum of the absolute values of the nine Wigner "
                    + "entries, minus one, as in Eq. (13). The definition applies to every "
                    + "complex 3 by 3 matrix without additional assumptions."),
            Describe.Lean(
                DescribeId.Create("qutrit-magic-coherence-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The pure-qutrit coherence bound"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Equation (18) asserts the bound for every normalized vector x in C cubed. "
                            + "Write rho = x x† = rankOneDensity(x), so rho has entry x(i) times "
                            + "the complex conjugate of x(j). Write C = l1Coherence(rho), the sum "
                            + "of the moduli of all ordered off-diagonal entries, hence:")),
                    new DocumentBlock.DisplayFormula(Disp(CoherenceFormula())),
                    Paragraph(Text(
                        "The normalization is the sum of squared moduli. The proposition "
                            + "requires no restriction on the phases."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qutrit-magic-coherence-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The lower bound holds for every pure qutrit"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let r(i) be the modulus of x(i). In column i of 3W, put A = r(i)² "
                            + "and R = r(j)r(k), where i, j, k are distinct. The three entries "
                            + "have sum 3A and second moment 3A² + 6R². For any three real "
                            + "numbers with positive mass P and negative mass N, the sum of "
                            + "their squares is at most P² + N². Applied to a column, this "
                            + "gives 3R² ≤ 3A² + 3AN + N² ≤ (√3 A + N)², "
                            + "so its negative mass is at least √3 max(R − A, 0).")),
                    Paragraph(Text(
                        "Set s = r(0)r(1) + r(0)r(2) + r(1)r(2) = C/2 and v = 1 − s. "
                            + "Normalization gives s ≥ 0 and v ≥ 0. The amplitude defects "
                            + "δ(i) = r(i)² − r(j)r(k) satisfy Σδ = v and Σδ² = 1 − s². "
                            + "Their negative mass D = Σ max(−δ(i), 0) therefore obeys "
                            + "1 − s² ≤ (v + D)² + D², which is D² + vD ≥ sv.")),
                    Paragraph(Text(
                        "Put T = (√3/2)s√v. The square identity "
                            + "sv − (T² + vT) = (sv/4)(√3√v − 1)² "
                            + "shows T² + vT ≤ sv ≤ D² + vD. Since T, D and v are "
                            + "nonnegative, D ≥ T. Finally, let N be the total negative mass "
                            + "of 3W. The column bounds give N ≥ √3 D. Since the entries "
                            + "of 3W sum to 3, M = sumNegativity(rho) = (2/3)N "
                            + "≥ (2/√3)D ≥ s√v. Substituting s = C/2 and v = 1 − s "
                            + "gives the asserted bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mukhopadhyay-sazim-pati-2018-qutrit-magic-coherence-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("qutrit-magic-coherence-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index() => Call("Fin", D(3));
    private static Formula Matrices() => Call("Matrix", Index(), Index(), Complexes());
    private static Formula Vectors() => Parenthesized(new Formula.TypeArrow(Index(), Complexes()));
    private static Formula Pure(Formula x) => Call("rankOneDensity", x);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(body));
    private static Formula Entry(byte i, byte j) => new Formula.Subscript(Rho, Seq(D(i), Comma, D(j)));
    private static Formula RealEntry(byte i, byte j) => Call("Re", Entry(i, j));
    private static Formula ImagEntry(byte i, byte j) => Call("Im", Entry(i, j));

    private static Formula WignerFormula()
    {
        Formula first(byte i, byte j, byte k) => Add(RealEntry(i, i), Mul(D(2), RealEntry(j, k)));
        Formula lower(byte i, byte j, byte k, bool plus)
        {
            Formula baseEntry = Subtract(RealEntry(i, i), RealEntry(j, k));
            Formula imaginary = Mul(Root(D(3)), ImagEntry(j, k));
            return plus ? Add(baseEntry, imaginary) : Subtract(baseEntry, imaginary);
        }
        Formula array = Seq(Begin, Grp(F.Id("pmatrix")),
            first(0, 1, 2), Amp, first(1, 0, 2), Amp, first(2, 0, 1), RowBreak,
            lower(0, 1, 2, false), Amp, lower(1, 0, 2, true), Amp, lower(2, 0, 1, false), RowBreak,
            lower(0, 1, 2, true), Amp, lower(1, 0, 2, false), Amp, lower(2, 0, 1, true),
            End, Grp(F.Id("pmatrix")));
        return All(Rho, Matrices(), Equal(Call("wigner", Rho), Mul(new Formula.Fraction(D(1), D(3)), array)));
    }

    private static Formula NegativityFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        Formula sum = SumOver(Typed(p, Index()), SumOver(Typed(q, Index()),
            new Formula.Absolute(Call("wigner", Rho, p, q))));
        return All(Rho, Matrices(), Equal(Call("sumNegativity", Rho), Subtract(sum, D(1))));
    }

    private static Formula CoherenceFormula()
    {
        Formula x = F.Id("x"), i = F.Id("i"), j = F.Id("j");
        Formula offDiagonal = Seq(Typed(j, Index()), Comma, Sp,
            new Formula.Relation(i, FormulaRelationOperator.NotEqual, j));
        Formula entry = Mul(At(x, i), Seq(Overline, Grp(At(x, j))));
        Formula sum = SumOver(Typed(i, Index()), SumOver(offDiagonal, new Formula.Absolute(entry)));
        return All(x, Vectors(), Equal(Call("l1Coherence", Pure(x)), sum));
    }

    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x"), i = F.Id("i");
        Formula norm = SumOver(Typed(i, Index()), new Formula.Power(new Formula.Absolute(At(x, i)), D(2)));
        Formula halfCoherence = new Formula.Fraction(Call("l1Coherence", Pure(x)), D(2));
        Formula bound = LE(Mul(halfCoherence, Root(Subtract(D(1), halfCoherence))), Call("sumNegativity", Pure(x)));
        Formula normalized = new Formula.Logic(Parenthesized(Equal(norm, D(1))),
            FormulaLogicOperator.Implies, Parenthesized(bound));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All(x, Vectors(), normalized)));
    }
}
