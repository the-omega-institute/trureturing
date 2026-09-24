using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class A331474HankelBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Constants/Moments/A331474HankelBridge.";
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/Recurrence/barry2020a331474");
    private static readonly LibraryNoteRef CatalanFamily =
        LibraryNoteRef.Create("D5/L/Recurrence/bojicicpetkovicbarry2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal A331473 moments and their A331474 Hankel determinants are connected "
            + "to a signed period-two continuant, yielding an exact all-order scalar bridge.",
        H("A331474 Signed Hankel Bridge"),
        Blocks(
            Paragraph(Text(
                "All indices below are natural numbers. Integer-valued sequences are written "
                    + "with subscripts. The symbol X is the polynomial indeterminate, coeff "
                    + "selects a polynomial coefficient, and det is the determinant of the "
                    + "displayed finite matrix. These definitions use the literal offset-zero "
                    + "OEIS source, not a recurrence-defined replacement for its Hankel transform.")),
            Node("b", "Unsigned Catalan-derivative moments", BFormula(),
                "The moment b(n) is exactly binomial(2n+2,n), equivalently "
                    + "(n+1) times the Catalan number of index n+1. It is the coefficient "
                    + "sequence obtained by differentiating the Catalan power series.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Oeis)),
            Node("s", "Literal alternating source sequence", SFormula(),
                "This is the full alternating binomial transform printed in A331473, with "
                    + "k ranging from zero through n and with no recurrence substituted for it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Oeis)),
            Node("H", "Literal Hankel determinant", HFormula(),
                "H(n) is the determinant of the actual (n+1)-square Hankel matrix of s. "
                    + "Consequently the final generating function is about PowerSeries.mk H, "
                    + "rather than a sequence introduced later by its recurrence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Oeis)),
            Node("a", "Period-two diagonal coefficient", AFormula(),
                "The source-specific monic continuant uses diagonal coefficient 4 at even "
                    + "indices and 0 at odd indices. This period-two tail is derived from the "
                    + "Catalan derivative equation.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("P", "Signed monic continuants", PFormula(),
                "The polynomials are monic: P(0)=1, P(1)=X-4, and "
                    + "P(m+2)=(X-a(m+1))P(m+1)+P(m). The plus sign gives signed squared "
                    + "norms (-1)^k; positivity is neither assumed nor true here.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("B", "Unsigned moment functional", FunctionalFormula("B", "b"),
                "B evaluates an integer polynomial by weighting every coefficient with b. "
                    + "The Catalan derivative equation supplies the two alternating tails used "
                    + "to prove orthogonality of the monic continuants.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("S", "Literal alternating moment functional", FunctionalFormula("S", "s"),
                "S evaluates a polynomial against the literal sequence s. The source relation "
                    + "b(n+1)=s(n+1)+s(n) transfers the unsigned Catalan identities to this "
                    + "signed functional.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("p", "Continuant constant terms", CoefficientFormula(),
                "The scalar p(n) is the constant coefficient of P(n). Its exact initial "
                    + "values and recurrence are included in the bridge theorem below.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("u", "Literal functional values", UFormula(),
                "The scalar u(n) is S(P(n)). Its exact initial values and source-specific "
                    + "recurrence are included in the bridge theorem below.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Oeis, CatalanFamily)),
            Node("literal_hankel_eq_signed_kernel", "Literal determinant equals the signed kernel",
                BridgeFormula(),
                "The Catalan derivative coefficients first give two period-two power-series "
                    + "tails. Their continuant error identity yields signed monomial "
                    + "orthogonality, which extends to polynomial orthogonality. The resulting "
                    + "monic coefficient matrix diagonalizes the Gram matrix with diagonal "
                    + "entries (-1)^k. Negative entries are intentional, so no positive-real "
                    + "Gram argument is used.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Oeis, CatalanFamily),
                "A division-free adjugate identity then replaces matrix inversion. For the "
                    + "actual adjacent-column coefficient c=-1, the Hankel determinant is "
                    + "converted to a Cramer determinant and then to the signed reproducing "
                    + "kernel. The same proof derives p(0)=1, p(1)=-4 and its recurrence, and "
                    + "u(0)=1, u(1)=-1, u(2)=1 and its quantified recurrence. No finite-prefix "
                    + "certificate or positivity hypothesis carries any part of the result."))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        string? secondParagraph = null)
    {
        var commentary = secondParagraph is null
            ? Blocks(Paragraph(Text(prose)))
            : Blocks(Paragraph(Text(prose)), Paragraph(Text(secondParagraph)));
        return Describe.Lean(
            DescribeId.Create("a331474-bridge-" + DescribeSuffix(name)),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            commentary,
            role);
    }

    private static string DescribeSuffix(string name) => name switch
    {
        "H" => "hankel-h",
        "P" => "polynomial-p",
        "B" => "functional-b",
        "S" => "functional-s",
        _ => name.Replace('_', '-').ToLowerInvariant(),
    };

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Sub(string name, Formula index) =>
        new Formula.Subscript(F.Id(name), index);
    private static Formula Apply(string name, Formula argument) => Call(name, argument);
    private static Formula Parenthesized(params Formula[] value) => Seq([Open, .. value, Close]);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(Formula body) =>
        Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Naturals(), Comma, Sp, body));
    private static Formula Equality(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Negative(Formula value) => Seq(Minus, value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);

    private static Formula BFormula()
    {
        Formula n = F.Id("n");
        return Universal(Equality(Sub("b", n), Call("binom", Add(Multiply(D(2), n), D(2)), n)));
    }

    private static Formula SFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula summand = Multiply(
            Power(Parenthesized(Minus, D(1)), Seq(n, Sp, Minus, Sp, k)),
            Call("binom", Add(Multiply(D(2), k), D(2)), k));
        Formula sum = Seq(Sum, Underscore, Grp(k, Sp, Eq, Sp, D(0)),
            Caret, Grp(n), Sp, summand);
        return Universal(Equality(Sub("s", n), sum));
    }

    private static Formula HFormula()
    {
        Formula n = F.Id("n");
        Formula entry = Sub("s", Seq(F.Id("i"), Sp, Plus, Sp, F.Id("j")));
        Formula matrix = Seq(Open, entry, Close, Underscore, Grp(
            D(0), Sp, Leq, Sp, F.Id("i"), Comma, F.Id("j"), Sp, Leq, Sp, n));
        return Universal(Equality(Sub("H", n), Call("det", matrix)));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Universal(Equality(Sub("a", n), Call("ite", Call("Even", n), D(4), D(0))));
    }

    private static Formula PFormula()
    {
        Formula m = F.Id("m");
        Formula next = Seq(m, Sp, Plus, Sp, D(1));
        Formula nextTwo = Seq(m, Sp, Plus, Sp, D(2));
        Formula recurrence = Equality(Sub("P", nextTwo),
            Add(Multiply(Parenthesized(F.Id("X"), Sp, Minus, Sp, Sub("a", next)),
                Sub("P", next)), Sub("P", m)));
        return Disp(new Formula.Aligned([
            Equality(Sub("P", D(0)), D(1)),
            Equality(Sub("P", D(1)), Seq(F.Id("X"), Sp, Minus, Sp, D(4))),
            Seq(Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp, recurrence)
        ]));
    }

    private static Formula FunctionalFormula(string functional, string moments)
    {
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula sum = Seq(Sum, Underscore, Grp(n, Sp, InMacro, Sp, Naturals()), Sp,
            Multiply(Call("coeff", f, n), Sub(moments, n)));
        return Disp(Seq(Forall, Sp, f, Sp, InMacro, Sp, Integers(), OpenBracket,
            F.Id("X"), CloseBracket, Comma, Sp, Equality(Call(functional, f), sum)));
    }

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        return Universal(Equality(Sub("p", n), Call("coeff", Sub("P", n), D(0))));
    }

    private static Formula UFormula()
    {
        Formula n = F.Id("n");
        return Universal(Equality(Sub("u", n), Apply("S", Sub("P", n))));
    }

    private static Formula BridgeFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula sign = Power(Parenthesized(Minus, D(1)), k);
        Formula product = Seq(Prod, Underscore, Grp(k, Sp, Eq, Sp, D(0)),
            Caret, Grp(n), Sp, sign);
        Formula kernel = Seq(Sum, Underscore, Grp(k, Sp, Eq, Sp, D(0)),
            Caret, Grp(n), Sp, sign, Sp, Sub("p", k), Sp, Sub("u", k));
        Formula pRec = Equality(Sub("p", Seq(m, Sp, Plus, Sp, D(2))),
            Add(Multiply(Negative(Sub("a", Seq(m, Sp, Plus, Sp, D(1)))),
                Sub("p", Seq(m, Sp, Plus, Sp, D(1)))), Sub("p", m)));
        Formula uRec = Equality(Sub("u", Seq(m, Sp, Plus, Sp, D(1))),
            Add(Multiply(Negative(Parenthesized(Sub("a", m), Sp, Plus, Sp, D(1))),
                Sub("u", m)), Sub("u", Seq(m, Sp, Minus, Sp, D(1)))));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Equality(Sub("H", n), Multiply(product, kernel)), Sp, Land),
            Seq(Equality(Sub("p", D(0)), D(1)), Sp, Land, Sp,
                Equality(Sub("p", D(1)), Negative(D(4))), Sp, Land),
            Seq(Open, Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                pRec, Close, Sp, Land),
            Seq(Equality(Sub("u", D(0)), D(1)), Sp, Land, Sp,
                Equality(Sub("u", D(1)), Negative(D(1))), Sp, Land, Sp,
                Equality(Sub("u", D(2)), D(1)), Sp, Land),
            Seq(Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                D(2), Sp, Leq, Sp, m, Sp, Rightarrow, Sp, uRec, Dot)
        ]));
    }
}
