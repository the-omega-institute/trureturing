using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandEtaDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");
    private static readonly LibraryNoteRef Sellers = LibraryNoteRef.Create("D5/L/Fourier/sellers2023designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity dissections of the designated-summand generating series and its inverse.",
        H("Integral reciprocal and square dissections"),
        Blocks(
            Paragraph(Text("The Jacobi product identities turn the parity dissection into an identity between Euler units. The coefficient map from integers to rationals is injective, so the reciprocal dissection holds integrally. Pairing odd Euler factors at q and −q gives the sign norm used to square F. The factor W reduces modulo four to f6 squared, which is supported on even degrees.")),
            Paragraph(Text("Lemma 2.2 of Yaqubi and Mirzavaziri gives the prime-power Frobenius congruence. The dyadic lift uses the iterated Frobenius over ZMod 2, then raises the integral congruence to the required modulus.")),
            Paragraph(Text("Write f_d for euler at degree d. Each quotient of Euler factors uses their units of constant coefficient one and is coerced back to a formal series.")),
            Node("reduce", "Reduce every integer coefficient modulo the given natural modulus.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                ReduceFormula()),
            Node("coeff_reduce_eq_zero", "A reduced coefficient vanishes exactly when the modulus divides the original coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_mod_eq_iff", "Two reductions coincide exactly when the constant series of the modulus divides the difference.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("reduce_lift", "For every integral formal series p(q) and natural j and r, the coefficientwise reduction of p(q)^(2^(j+1+r)) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("reduce_lift_mul", "For every integral formal series p(q) and natural j, r and t, the coefficientwise reduction of p(q)^(2^(j+1+r)·t) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j·t) at the same modulus.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("H", "The inverse unit of the generating series F.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                Define(F.Id("H"), new Formula.Fraction(Product(Euler(1), Euler(2), Euler(3)), Euler(6)))),
            Node("H0", "The Euler quotient f1^2 f4^2 f6^4 divided by f2^2 f3^2 f12^2, whose degree doubling is the even part of H over the integers.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                Define(new Formula.Subscript(F.Id("H"), F.D(0)), new Formula.Fraction(
                    Product(Euler(1, 2), Euler(4, 2), Euler(6, 4)), Product(Euler(2, 2), Euler(3, 2), Euler(12, 2))))),
            Node("T", "The Euler quotient f1^4 f6^2 divided by f2^2 f3^2. Over the integers, the odd part of H is −q T(q⁴).", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                Define(F.Id("T"), new Formula.Fraction(Product(Euler(1, 4), Euler(6, 2)), Product(Euler(2, 2), Euler(3, 2))))),
            Node("FH", "The product of F and H is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("H_dissection", "Over the integers, H(q) is H0(q²) minus q T(q⁴). Sellers Lemma 2.3 gives the classical two-dissection of f1 f3. Multiplying that identity by the even unit f2/f6 gives the identity for H. The Lean proof derives the product dissection from the Jacobi identities and descends through the injective map from integer to rational coefficients.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Sellers)),
            Node("H_support", "The integral coefficient of H in degree 4n+3 vanishes for every natural n.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("E", "The integral series such that E(q²) is the even part of F(q) squared. Here N is the underlying series of the unit quotient f2 f6/(f1^5 f3).", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                EFormula()),
            Node("W", "The integral Euler quotient f2^4 f6^4 divided by f1^8 f3^4.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Define(F.Id("W"), new Formula.Fraction(Product(Euler(2, 4), Euler(6, 4)), Product(Euler(1, 8), Euler(3, 4))))),
            Node("F_square", "Over the integers, F(q) squared is E(q²) plus 2q W(q²).", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("W_support", "For every natural n, the coefficient of degree 2n+1 in the integral series W is divisible by four.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("designatedsummandetadissection-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(narrative))), role);

    private static Formula ReduceFormula()
    {
        var modulus = F.Id("m");
        var degree = F.Id("n");
        var power = new Formula.Power(F.Id("q"), degree);
        var index = new Formula.Subscript(F.Sum, F.Seq(degree, F.Ge, F.D(0)));
        var coefficient = new Formula.Subscript(F.Id("a"), degree);
        var reduced = new Formula.Subscript(F.Seq(F.Overline, F.Grp(coefficient)), modulus);
        return Define(Call("reduce", modulus, F.Seq(index, F.Sp, coefficient, F.Thin, power)),
            F.Seq(index, F.Sp, reduced, F.Thin, power));
    }

    private static Formula EFormula()
    {
        var q = F.Id("q");
        var h0 = new Formula.Apply(new Formula.Subscript(F.Id("H"), F.D(0)), [q]);
        var dilatedT = Call("T", Square(q));
        var norm = Call("N", q);
        var evenPart = F.Seq(Square(h0), F.Sp, F.Plus, F.Sp, q, F.Thin, Square(dilatedT));
        var normQuotient = new Formula.Fraction(Product(Euler(2), Euler(6)), Product(Euler(1, 5), Euler(3)));
        return F.Disp(F.Seq(Call("E", q), F.Sp, F.Colon, F.Eq, F.Sp,
            Square(norm), F.Thin, F.Open, evenPart, F.Close,
            F.Comma, F.Quad, norm, F.Sp, F.Colon, F.Eq, F.Sp, normQuotient));
    }

    private static Formula Square(Formula value) => new Formula.Power(value, F.D(2));
    private static Formula Euler(byte degree, byte exponent = 1)
    {
        var factor = new Formula.Subscript(F.Id("f"), Num(degree));
        return exponent == 1 ? factor : new Formula.Power(factor, F.D(exponent));
    }

    private static Formula Product(params Formula[] factors) => F.Seq(factors);

    private static Formula Define(Formula left, Formula right) =>
        F.Disp(F.Seq(left, F.Sp, F.Colon, F.Eq, F.Sp, right));
}
