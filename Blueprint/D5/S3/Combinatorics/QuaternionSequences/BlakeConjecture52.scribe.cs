using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QuaternionSequences;

internal sealed class BlakeConjecture52Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/blake2026perfectquaternionsequences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q₈ sequences of length at least two and Q₈ arrays with a first axis of length at least two and an odd transverse cardinality have a nonzero off-period autocorrelation for each noncentral twist.",
        H("Blake's Noncentral Twist Conjecture"),
        Blocks(
            Definition("Noncentral", "The six noncentral twists", NoncentralFormula(),
                "The coordinates are ordered by the real component and the coefficients of i, j and k. "
                + "The displayed three coordinate units and their negatives are the six twists of Conjecture 5.2."),
            Definition("IsQ8", "The quaternion alphabet", AlphabetFormula(),
                "The eight letters are the central units 1 and −1 and the six noncentral units. "
                + "Their integer coordinates carry Hamilton multiplication and quaternion conjugation. "
                + "The inclusion into the real Hamilton quaternions preserves these operations and is injective coordinatewise."),
            Definition("extension", "Right-twisted extension", ExtensionFormula(),
                "The positive length proof hM and the noncentrality proof hu are implicit in the display. "
                + "For any integer n, Euclidean division by the positive length gives n = qM + r with 0 ≤ r < M. "
                + "The definition uses that remainder as the sequence index. It multiplies on the right by the integer power "
                + "of the twist unit, whose inverse is its quaternion conjugate. Thus the formula holds for negative q as well."),
            Definition("correlation", "Twisted quaternion autocorrelation", CorrelationFormula(),
                "The summation runs over Fin M and casts the summation index to an integer inside the extension. "
                + "The star is quaternion conjugation. For a positive shift below M each wrapped term is "
                + "the product of the original letter, the conjugate of u, and the conjugate of the wrapped letter, in that order."),
            Describe.Lean(DescribeId.Create("blake-conjecture-5-2"),
                DeclarationHandle.Create(Prefix + "blake_conjecture_5_2"),
                H("Nonvanishing at a positive off-period shift"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 5.2 states \"No sequence of length M ≥ 2 over Q₈ has type ±i, ±j or ±k.\" "
                        + "A positive integer shift below M is off-period, so the displayed existence statement excludes the asserted type.")),
                    Paragraph(Text(
                        "Suppose that the correlations vanish at all positive shifts below M. The shift-one correlation "
                        + "maps to M in the field with two elements under the character that sends every letter to one. "
                        + "Hence M is even. Write M = dm with d its power-of-two part and m odd.")),
                    Paragraph(Text(
                        "In the polynomial quotient by T to the power 2d, put W = 1 + T and V equal to one plus the d-th power of T. "
                        + "Characteristic two gives V = W to the power d and V squared equals one, so W to the power M equals V. "
                        + "A Hamilton quaternion algebra homomorphism sends i and k to V and j to one for the i and k twists. "
                        + "For the j twists it sends j and k to V and i to one. It identifies both signs and preserves the "
                        + "image of a letter under conjugation.")),
                    Paragraph(Text(
                        "Form two weighted sums of the mapped letters with exponents r and M − 1 − r. "
                        + "Group the terms in the product by the difference of the two indices modulo M. "
                        + "A wrapped term has M extra powers of W, exactly the factor V in the mapped correlation. "
                        + "The off-diagonal groups therefore vanish. The diagonal is M times W to the power M − 1, which is zero.")),
                    Paragraph(Text(
                        "Lift each letter to a polynomial of the form one or one plus T to the power d. "
                        + "Through degree d − 1 both factors have the coefficients of the same geometric sum. "
                        + "Multiplication by T sends that geometric sum to W to the power M minus one, "
                        + "which is T to the power d in the quotient. Each factor has its first nonzero coefficient "
                        + "at degree d − 1, with value one. Their product has coefficient one at degree 2d − 2, "
                        + "which survives the quotient and contradicts its vanishing."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("blake-noncentral-quaternion-twist"),
                    ResolutionKind.Proved)),
            ArrayDefinition("baseCorrelation", "Right-twisted base correlation", false,
                "Definition 2.1 of Blake, arXiv:2611.20804v1, extends the first axis on the right. "
                + "At each transverse coordinate t the existing extension acts on the column indexed by t. "
                + "The transverse coordinate of the shifted entry is t plus sigma in the finite additive group. "
                + "The first-axis shift tau is read as its integer representative between zero and M minus one."),
            ArrayDefinition("fullPeriodCorrelation", "Autocorrelation over the full extension period", true,
                "The three indices enumerate the period of first-axis length 4M as qM plus r, with q in Fin 4 "
                + "and r in Fin M, and the transverse coordinate t in T. The star is quaternion conjugation. "
                + "In equation (2.1) each of the two lifted entries has its block factor on the right. "
                + "Taking the star of the second entry brings the two factors together in the order "
                + "u to the power q followed by its conjugate. Their product is one, giving four times the base correlation."),
            Describe.Lean(DescribeId.Create("blake-odd-transverse-nonvanishing"),
                DeclarationHandle.Create(Prefix + "odd_transverse_nonvanishing"),
                H("Nonvanishing for odd transverse cardinality"),
                StatementSource.FromAuthor(Disp(ArrayTheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first question in Section 9 of Blake, arXiv:2611.20804v1, asks which shapes admit "
                        + "arrays of noncentral type. Products of positive cyclic axes of odd cardinality give "
                        + "the finite additive groups in the statement. A shift different from the zero pair "
                        + "is off-period because the first coordinate is represented in the range zero through M minus one.")),
                    Paragraph(Text(
                        "If every off-period base correlation vanishes, the trivial character at the shift "
                        + "with first coordinate one and transverse coordinate zero gives M times the cardinality "
                        + "of T equal to zero in characteristic two. Thus M is even. For every fixed first-axis "
                        + "shift, summing the character images over all transverse shifts pairs each transverse "
                        + "entry with every entry in the other column. The wrap factor depends only on the two "
                        + "first-axis indices. The zero shift contributes the diagonal M times the cardinality of T.")),
                    Paragraph(Text(
                        "Let d be the power-of-two part of M. Use a character sending the twist to one plus "
                        + "X to the power d in the quotient by X to the power 2d. Odd transverse cardinality "
                        + "makes each column sum lift to one plus a multiple of X to the power d. "
                        + "The aggregated correlations force the cyclic product of the two weighted column sums "
                        + "to vanish. Its coefficient at degree 2d minus two is one, a contradiction. "
                        + "The factor four gives the same nonzero shift for the full period, since the "
                        + "quaternions have integer coordinates.")),
                    Paragraph(Text(
                        "This excludes the odd-transverse family with first length at least two. "
                        + "The even transverse shapes, including the paper's two-by-two example, lie outside this family."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("blake-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Quaternions() => Call("Quaternion", Z());
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Tuple(Formula a, Formula b, Formula c, Formula d) =>
        Seq(Langle, a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, d, Rangle);
    private static Formula Negative(Formula f) => Seq(Minus, f);
    private static Formula Letter(Formula s, Formula r) => new Formula.Apply(s, [r]);

    private static Formula NoncentralFormula()
    {
        Formula u = F.Id("u"), zero = D(0), one = D(1);
        Formula i = Tuple(zero, one, zero, zero);
        Formula j = Tuple(zero, zero, one, zero);
        Formula k = Tuple(zero, zero, zero, one);
        return IffOf(Call("Noncentral", u),
            Or(Equal(u, i), Or(Equal(u, Negative(i)), Or(Equal(u, j),
                Or(Equal(u, Negative(j)), Or(Equal(u, k), Equal(u, Negative(k))))))));
    }

    private static Formula AlphabetFormula()
    {
        Formula u = F.Id("u");
        return IffOf(Call("IsQ8", u),
            Or(Equal(u, D(1)), Or(Equal(u, Negative(D(1))), Call("Noncentral", u))));
    }

    private static Formula ExtensionFormula()
    {
        Formula m = F.Id("M"), q = F.Id("q"), r = F.Id("r"), s = F.Id("s"), u = F.Id("u");
        return Equal(Call("extension", s, u, Add(Mul(q, m), r)),
            Mul(Letter(s, r), new Formula.Power(u, q)));
    }

    private static Formula CorrelationFormula()
    {
        Formula m = F.Id("M"), r = F.Id("r"), s = F.Id("s"), u = F.Id("u");
        Formula term = Mul(Letter(s, r),
            Call("star", Call("extension", s, u, Add(r, Tau))));
        return Equal(Call("correlation", s, u, Tau),
            Seq(new Formula.Subscript(Sum, Seq(r, Colon, Call("Fin", m))), Sp, term));
    }

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("M"), r = F.Id("r"), s = F.Id("s"), u = F.Id("u");
        Formula indices = Call("Fin", m);
        Formula witness = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("tau"), Z(),
            And(Rel(D(0), FormulaRelationOperator.LessThan, F.Id("tau")),
                And(Rel(F.Id("tau"), FormulaRelationOperator.LessThan, m),
                    And(new Formula.Not(Par(Rel(m, FormulaRelationOperator.Divides, F.Id("tau")))),
                        Rel(Call("correlation", s, u, F.Id("tau")), FormulaRelationOperator.NotEqual, D(0))))));
        return All("M", N(), Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            All("s", Seq(indices, Sp, To, Sp, Quaternions()),
                Imp(Par(All("r", indices, Call("IsQ8", Letter(s, r)))),
                    All("u", Quaternions(), Imp(Call("Noncentral", u), witness))))));
    }

    private static DocumentBlock ArrayDefinition(string name, string title, bool full, string prose) =>
        Describe.Lean(DescribeId.Create("blake-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(ArrayCorrelationFormula(name, full))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula WithArrayInputs(Formula sizeCondition, Formula body)
    {
        Formula t = F.Id("T"), m = F.Id("M"), u = F.Id("u"), indices = Call("Fin", m);
        Formula arrayType = Seq(indices, Sp, To, Sp, t, Sp, To, Sp, Quaternions());
        return All("T", F.Id("Type"),
            Seq(OpenBracket, Call("Fintype", t), CloseBracket, Sp,
                OpenBracket, Call("AddCommGroup", t), CloseBracket, Sp,
                All("M", N(), Imp(sizeCondition, All("A", arrayType,
                    All("u", Quaternions(), Imp(Call("Noncentral", u), body)))))));
    }

    private static Formula ArrayEntry(Formula r, Formula t) => new Formula.Apply(F.Id("A"), [r, t]);
    private static Formula Column(Formula t) =>
        Par(Seq(F.Id("j"), Sp, Mapsto, Sp, ArrayEntry(F.Id("j"), t)));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula SumOver(Formula index, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Colon, type)), Sp, body);

    private static Formula ArrayCorrelationFormula(string name, bool full)
    {
        Formula m = F.Id("M"), r = F.Id("r"), t = F.Id("t"), q = F.Id("q");
        Formula u = F.Id("u"), tau = F.Id("tau"), sigma = F.Id("sigma"), transverse = F.Id("T");
        Formula indices = Call("Fin", m);
        Formula index = full ? Add(Mul(q, m), r) : r;
        Formula left = full ? Call("extension", Column(t), u, index) : ArrayEntry(r, t);
        Formula right = Call("star", Call("extension", Column(Add(t, sigma)), u, Add(index, tau)));
        Formula sum = SumOver(r, indices, SumOver(t, transverse, Mul(left, right)));
        if (full)
            sum = SumOver(q, Call("Fin", D(4)), sum);
        Formula formula = All("tau", indices, All("sigma", transverse,
            Equal(Call(name, F.Id("A"), u, tau, sigma), sum)));
        return WithArrayInputs(Rel(D(0), FormulaRelationOperator.LessThan, m), formula);
    }

    private static Formula ArrayTheoremFormula()
    {
        Formula m = F.Id("M"), u = F.Id("u"), a = F.Id("A"), indices = Call("Fin", m);
        Formula tau = F.Id("tau"), sigma = F.Id("sigma"), transverse = F.Id("T"), zero = D(0);
        Formula entries = All("r", indices, All("t", transverse,
            Call("IsQ8", ArrayEntry(F.Id("r"), F.Id("t")))));
        Formula witness = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("tau"), indices,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("sigma"), transverse,
                And(Rel(Pair(tau, sigma), FormulaRelationOperator.NotEqual, Pair(zero, zero)),
                    And(Rel(Call("baseCorrelation", a, u, tau, sigma), FormulaRelationOperator.NotEqual, zero),
                        Rel(Call("fullPeriodCorrelation", a, u, tau, sigma), FormulaRelationOperator.NotEqual, zero)))));
        return WithArrayInputs(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            Imp(Par(entries), witness));
    }
}
