using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class InverseGeometricIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted symmetry and inversion of the spectral geometric mean.",
        H("InverseGeometricIdentification"), Blocks(
            Describe.Lean(DescribeId.Create("unitary-rpow"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/InverseGeometricIdentification.unitary_rpow"),
                H("Unitary equivariance of real powers"), StatementSource.FromAuthor(Equivariance()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every ordered complex C-star algebra, conjugation by a "
                    + "unitary intertwines every real spectral power of a strictly positive "
                    + "element. The conjugation is a star algebra automorphism; the continuous "
                    + "functional calculus is applied only to that automorphism. An arbitrary "
                    + "invertible congruence does not have this property."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-mean-identification"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Hiai/InverseGeometricIdentification.geometricMean_identification"),
                H("Weighted symmetry and inverse sandwich"), StatementSource.FromAuthor(Identification()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/hiai2025geometricidentification")),
                Blocks(Paragraph(Text("For arbitrary finite complex square matrices X and Y "
                    + "that are positive definite, define G(t,X,Y) by the existing geometricMean: "
                    + "X to exponent one half, then the t-th spectral power of X to exponent "
                    + "minus one half times Y times X to exponent minus one half, then X to "
                    + "exponent one half. The base is the first matrix argument. For every real "
                    + "t, G(t,X,Y)=G(1-t,Y,X) and G(-t,X,Y)=X inverse(G(t,X,Y)) X.")),
                    Paragraph(Text("Put C=X to exponent minus one half times Y times X to "
                    + "exponent minus one half. The unitary U=Y to exponent minus one half "
                    + "times X to exponent one half times C to exponent one half identifies "
                    + "the reversed normalization with U inverse(C) U adjoint. Unitary "
                    + "equivariance then turns its exponent 1-t into the conjugate of C to "
                    + "exponent t-1. Restoring the outer square roots combines powers of the "
                    + "same C to recover G(t,X,Y). No X/Y commutation is assumed.")),
                    Paragraph(Text("The inverse sandwich follows from inversion of the "
                    + "square-root congruence and inverse(C to exponent t)=C to exponent "
                    + "minus t. At t=0 this uses the unit spectral power, so the endpoint is "
                    + "included. Empty matrix dimension is also included. Matrix nonsingular "
                    + "inverse agrees with Ring.inverse by Matrix.nonsing_inv_eq_ringInverse.")),
                    Paragraph(Text("Substitution t=-theta gives G(1+theta,Y,X)=G(-theta,X,Y), "
                    + "including theta=0 and theta=1. These are classical geometric-mean "
                    + "identities. In Hiai Problem 5.18 they connect the inverse-mean variational "
                    + "formula to the positive-weight mean-trace concavity. Joint convexity "
                    + "assembly and the common-epsilon support-preserving positive semidefinite "
                    + "extension are additional mathematical obligations."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula Bind(Formula type, string[] names, Formula body)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(Id(names[i]));
        }
        items.AddRange([Colon, Sp, type, Comma, Esc, body]);
        return Seq([.. items]);
    }
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Eq, right);
    private static Formula Prod(params Formula[] factors) => Seq(factors);
    private static Formula Adj(Formula x) => Call("star", x);
    private static Formula Power(Formula x, Formula t) => Call("rpow", x, t);
    private static Formula Mean(Formula t, Formula x, Formula y) => Call("geometricMean", t, x, y);

    private static Formula Equivariance()
    {
        var a = Id("A"); var x = Id("a"); var u = Id("U"); var t = Id("t");
        return Bind(Call("Level"), ["v"], Bind(Call("Type", Id("v")), ["A"],
            Seq(OpenBracket, Call("CStarAlgebra", a), CloseBracket, Comma, Sp,
                OpenBracket, Call("PartialOrder", a), CloseBracket, Comma, Sp,
                OpenBracket, Call("StarOrderedRing", a), CloseBracket, Comma, Esc,
                Bind(Call("unitary", a), ["U"], Bind(a, ["a"], Bind(Real, ["t"],
                    Seq(Call("IsStrictlyPositive", x), Implies, Esc,
                        Eqn(Power(Prod(u, x, Adj(u)), t), Prod(u, Power(x, t), Adj(u))))))))));
    }

    private static Formula Identification()
    {
        var d = Id("d"); var x = Id("X"); var y = Id("Y"); var t = Id("t");
        var matrix = Call("Matrix", d, d, Complex);
        return Bind(Call("Level"), ["v"], Bind(Call("Type", Id("v")), ["d"],
            Seq(OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
                Bind(matrix, ["X", "Y"], Bind(Real, ["t"],
                    Seq(Call("PosDef", x), Land, Sp, Call("PosDef", y), Implies, Esc,
                        Eqn(Mean(t, x, y), Mean(Seq(D(1), Minus, t), y, x)), Land, Sp,
                        Eqn(Mean(Seq(Minus, t), x, y),
                            Prod(x, Call("inverse", Mean(t, x, y)), x))))))));
    }
}
