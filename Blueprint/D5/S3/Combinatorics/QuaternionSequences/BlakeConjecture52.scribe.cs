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
        "Every quaternion sequence of length at least two has a nonzero off-period autocorrelation for each noncentral twist.",
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
}
