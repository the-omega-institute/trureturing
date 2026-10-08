using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FreeSpectrahedronFeasibilityWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six real symmetric matrices of Appendix A.1 are positive semidefinite over the "
            + "complex numbers and satisfy all four affine constraints throughout the closed interval.",
        H("The Appendix A.1 feasible tuple"),
        Blocks(
            Node("xone", "X₁", "The first real matrix is diagonal with entries 1 and -2.",
                "X₁", Eqn(X(1), Mat(D(1), D(0), D(0), Seq(Minus, D(2))))),
            Node("xtwo", "X₂", "The second real matrix is diagonal with entries -2 and 1.",
                "X₂", Eqn(X(2), Mat(Seq(Minus, D(2)), D(0), D(0), D(1)))),
            Node("xthree", "X₃", "For a real angle, the third matrix has cosine on the "
                + "first diagonal entry, negative cosine on the second, and sine off the diagonal.",
                "X₃", Angle(Eqn(XAngle(), Mat(Cosine(), Sine(), Sine(), Seq(Minus, Cosine()))))),
            Node("gamma", "The normalization constant", "The scalar gamma is the inclusion "
                + "constant in Theorem 5.6 of Bluhm, Evert, Klep, Magron and Nechita, arXiv:2512.17706.",
                "γ", Eqn(GammaLower, Fr(D(4), Seq(D(1), Plus, RootThree())))),
            Node("beta", "The radical", "The principal real square roots define beta for "
                + "every real angle. This is the expression in arXiv:2512.17706, Appendix A.1.",
                "β", Angle(Eqn(BetaAngle(), Seq(RootThree(), Sp, Sqrt, Grp(Radicand()))))),
            Node("cone", "C₁", "The first matrix is a positive scalar multiple of the "
                + "all-ones matrix on the stated interval.",
                "C₁", Eqn(Ci(1), Scale(Seq(Open, Fr(D(1), RootThree()), Minus,
                    Fr(D(1), D(2)), Close), Mat(D(1), D(1), D(1), D(1))))),
            Node("ctwo", "C₂", "The second matrix is the explicit candidate in "
                + "arXiv:2512.17706, Appendix A.1. Its determinant is nonnegative, "
                + "including at the right endpoint where it vanishes.",
                "C₂", Angle(Eqn(Ci(2), Scale(Fr(D(1), D(1, 2)), Mat(
                    Seq(D(3), Sp, Cosine(), Plus, D(8), Sp, RootThree(), Minus, D(9), Minus, BetaAngle()),
                    OffDiagonal(), OffDiagonal(),
                    Seq(Minus, D(3), Sp, Cosine(), Plus, D(8), Sp, RootThree(), Minus, D(3), Minus, BetaAngle())))))),
            Node("cthree", "C₃", "Equation (47) determines the third matrix from the first "
                + "two matrices, X₃ and the normalization constant.",
                "C₃", Angle(Eqn(Ci(3), Seq(Minus, Ci(1), Minus, Ci(2), Plus,
                    Scale(Fr(D(1), D(2)), XAngle()), Plus, Scale(Fr(GammaLower, D(2)), Identity()))))),
            Node("cfour", "C₄", "Equation (47) determines the fourth matrix. Its value "
                + "is independent of the real angle.",
                "C₄", Angle(Eqn(Ci(4), Seq(Minus, Ci(1), Plus, Scale(Fr(D(1), D(3)), X(1)),
                    Plus, Scale(Fr(D(1), D(3)), X(2)), Plus, Scale(Fr(GammaLower, D(3)), Identity()))))),
            Node("cfive", "C₅", "Equation (47) determines the fifth matrix from C₂, X₁ and gamma.",
                "C₅", Angle(Eqn(Ci(5), Seq(Minus, Ci(2), Minus, Scale(Fr(D(1), D(3)), X(1)),
                    Plus, Scale(Fr(GammaLower, D(3)), Identity()))))),
            Node("csix", "C₆", "Equation (47) determines the sixth matrix from C₁, C₂, "
                + "X₂, X₃ and gamma.",
                "C₆", Angle(Eqn(Ci(6), Seq(Ci(1), Plus, Ci(2), Minus, Scale(Fr(D(1), D(3)), X(2)),
                    Minus, Scale(Fr(D(1), D(2)), XAngle()), Minus, Scale(Fr(GammaLower, D(6)), Identity()))))),
            Node("family", "The indexed family", "The indices 0 through 5 correspond "
                + "in order to C₁ through C₆. Every value is a real 2 by 2 matrix.",
                "C", All(F.Id("i"), Fin(6), Angle(Eqn(CAt(F.Id("i")), Seq(
                    Open, Ci(1), Comma, Sp, Ci(2), Comma, Sp, Ci(3), Comma, Sp,
                    Ci(4), Comma, Sp, Ci(5), Comma, Sp, Ci(6), Close, Underscore, Grp(F.Id("i"))))))),
            Node("claim", "Appendix A.1 feasibility", "Bluhm, Evert, Klep, Magron and "
                + "Nechita, arXiv:2512.17706, Appendix A.1, conjecture feasibility of this "
                + "specific tuple for every angle in [0, pi/2]. SDP (37) consists of "
                + "positive semidefiniteness of the six complex images and the four displayed "
                + "affine equations. The map uses the standard real-to-complex inclusion; "
                + "the identity is the real 2 by 2 identity matrix. Positive semidefiniteness "
                + "requires nonnegative determinants.",
                "claim", Seq(F.Id("claim"), Sp, Colon, Eq, Sp, ClaimBody())),
            Describe.Lean(
                DescribeId.Create("appendix-feasibility-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Feasibility throughout the closed interval"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Appendix A.1 conjecture of arXiv:2512.17706 is proved. Equation (47) "
                        + "gives the four affine identities. A real symmetric 2 by 2 matrix with "
                        + "positive trace and nonnegative determinant has a nonnegative complex "
                        + "quadratic form. The first and fourth matrices have positive trace and "
                        + "zero determinant, as do the third and fifth. For the second matrix, "
                        + "squaring and factoring the radical comparison gives a product of "
                        + "1 minus sine with a strictly positive factor. Its determinant is "
                        + "therefore nonnegative and its trace is positive. The sixth matrix "
                        + "has the same trace and determinant as the second."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bluhm-2025-appendix-a1-feasibility"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string prose,
        string declaration, Formula formula) => declaration is "C" or "claim"
        ? Describe.Lean(
            DescribeId.Create("appendix-feasibility-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition)
        : Describe.Remark(
            DescribeId.Create("appendix-feasibility-" + id), H(title), Disp(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(byte n) => App("Fin", D(n));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, name, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Angle(Formula body) => All(Theta, Reals(), body);
    private static Formula Eqn(Formula lhs, Formula rhs) => Seq(lhs, Sp, Eq, Sp, rhs);
    private static Formula App(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Arguments(arguments), Close);
    private static Formula Arguments(Formula[] arguments) => arguments.Length switch
    {
        1 => arguments[0],
        2 => Seq(arguments[0], Comma, Sp, arguments[1]),
        _ => Seq(arguments[0], Comma, Sp, arguments[1], Comma, Sp, arguments[2])
    };
    private static Formula Fr(Formula top, Formula bottom) => Seq(F.Frac, Grp(top), Grp(bottom));
    private static Formula RootThree() => Seq(Sqrt, Grp(D(3)));
    private static Formula Cosine() => App("cos", Theta);
    private static Formula Sine() => App("sin", Theta);
    private static Formula BetaAngle() => Seq(Beta, Open, Theta, Close);
    private static Formula X(byte n) => Seq(F.Id("X"), Underscore, Grp(D(n)));
    private static Formula XAngle() => Seq(X(3), Open, Theta, Close);
    private static Formula Ci(byte n) => n == 1
        ? Seq(F.Id("C"), Underscore, Grp(D(n)))
        : Seq(F.Id("C"), Underscore, Grp(D(n)), Open, Theta, Close);
    private static Formula CAt(Formula i) => App("C", i, Theta);
    private static Formula CAt(byte i) => CAt(D(i));
    private static Formula Identity() => Seq(F.Id("I"), Underscore, Grp(D(2)));
    private static Formula Scale(Formula scalar, Formula matrix) => Seq(scalar, Sp, Cdot, Sp, matrix);
    private static Formula Mat(Formula u, Formula v, Formula z, Formula w) => Seq(
        Begin, Grp(F.Id("pmatrix")), u, Sp, Amp, Sp, v, RowBreak,
        z, Sp, Amp, Sp, w, End, Grp(F.Id("pmatrix")));
    private static Formula Radicand() => Seq(
        Open, D(6), Minus, D(4), Sp, RootThree(), Close, Sp, Sine(),
        Plus, D(6), Sp, Cosine(), Minus, D(4), Sp, RootThree(), Plus, D(1, 3));
    private static Formula OffDiagonal() => Seq(D(3), Sp, Sine(), Minus, D(2), Sp, RootThree(), Plus, D(3));
    private static Formula ClaimBody() => Angle(Seq(
        Open, F.Id("h"), Colon, Sp, Theta, Sp, InMacro, Sp,
        App("Icc", D(0), Fr(Pi, D(2))), Close, Sp, Rightarrow, Sp,
        Open, All(F.Id("i"), Fin(6),
            App("PosSemidef", App("map", F.Id("ofReal"), CAt(F.Id("i"))))), Close, Sp, Land, Sp,
        Eqn(Seq(CAt(0), Minus, Scale(D(2), CAt(1)), Plus, CAt(2), Plus, CAt(3),
            Minus, Scale(D(2), CAt(4)), Plus, CAt(5)), X(1)), Sp, Land, Sp,
        Eqn(Seq(CAt(0), Plus, CAt(1), Minus, Scale(D(2), CAt(2)), Plus, CAt(3),
            Plus, CAt(4), Minus, Scale(D(2), CAt(5))), X(2)), Sp, Land, Sp,
        Eqn(Seq(CAt(0), Plus, CAt(1), Plus, CAt(2), Minus, CAt(3), Minus, CAt(4), Minus, CAt(5)),
            XAngle()), Sp, Land, Sp,
        Eqn(Seq(Sum, Underscore, Grp(F.Id("i"), Colon, Sp, Fin(6)), Sp, CAt(F.Id("i"))),
            Scale(GammaLower, Identity()))));
}
