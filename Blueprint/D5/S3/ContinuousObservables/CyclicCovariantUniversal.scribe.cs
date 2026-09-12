using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class CyclicCovariantUniversalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous matrix fields represent every cyclic covariant pair in a unital complex C-star algebra.",
        H("The Universal Cyclic Covariant Algebra"),
        Blocks(
            Paragraph(Text(
                "Let M be a positive integer, I = Z/MZ, and A_0 the continuous complex "
                + "functions on the finite discrete set I. Let B_M be all continuous I by I "
                + "complex matrix fields on AddCircle 1, with the supremum of the L2 operator "
                + "norm. The homeomorphism from AddCircle 1 to the unit circle sends t to "
                + "the winding coordinate z(t). Define D(f) to be the constant diagonal "
                + "field, and S_M to have entry one in row j+1, column j, with the wrap "
                + "entry in row zero multiplied by z. For M = 1, S_1 = z.")),
            Paragraph(Text(
                "The integer action is alpha_n(f)(i) = f(i-n). Throughout, B is any unital "
                + "complex C-star algebra, pi is a unital complex star homomorphism from "
                + "A_0 to B, and v is unitary with v pi(f) v* = pi(alpha_1(f)) for every f. "
                + "The construction includes nonfaithful representations, arbitrary target "
                + "dimension, and proper spectra of v to the M-th power.")),
            Describe.Lean(
                DescribeId.Create("direct-continuous-field-lift"),
                Handle("cyclic_covariant_lift"),
                H("A lift defined on every continuous matrix field"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call(Theta, F.Id("F")), Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp,
                    Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, F.Id("I")), Sp,
                    Call(Sub(Op("chi"), F.Id("w")),
                        Sub(F.Id("F"), Seq(F.Id("i"), F.Id("j")))), Sp,
                    Sub(F.Id("E"), Seq(F.Id("i"), F.Id("j")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set w = v^M and p_i = pi(delta_i). Using the representatives from "
                        + "zero through M-1, set E_ij = v^i p_0 (v^j)*. Covariance gives "
                        + "orthogonal projection supports, hence E_ij E_kl = delta_jk E_il, "
                        + "E_ij* = E_ji, and the diagonal sum is one.")),
                    Paragraph(Text(
                        "For a continuous scalar coefficient, chi_w first restricts along "
                        + "spectrum(w) into the circle and its inverse parameter homeomorphism, "
                        + "then applies continuous functional calculus. Its values commute "
                        + "with the E_ij because w and w* do. This proves multiplication and "
                        + "star preservation of the finite matrix assembly. Centrality in "
                        + "the whole target algebra and equality of spectrum(w) with the "
                        + "circle are unnecessary. Automatic contractivity applies to the "
                        + "resulting star homomorphism on the complete field algebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-lift-preserves-readouts"),
                Handle("cyclic_covariant_lift_readout"),
                H("Every readout is preserved"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Sp, InMacro, Sp, Sub(F.Id("A"), D(0)), Comma, Sp,
                    Call(Theta, Call(F.Id("D"), F.Id("f"))), Sp, Eq, Sp,
                    Call(Pi, F.Id("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal coefficients are constant scalar functions. Functional "
                    + "calculus sends them to the scalar algebra map, while E_ii = p_i. "
                    + "The finite delta-function expansion therefore recovers pi(f)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-lift-preserves-winding-update"),
                Handle("cyclic_covariant_lift_update"),
                H("The winding update is preserved"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call(Theta, Sub(F.Id("S"), F.Id("M"))), Sp, Eq, Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary successor entries contribute E_(j+1,j). At the wrap, "
                    + "functional calculus sends z to v^M. Each contribution is v p_j, "
                    + "including the single wrap contribution when M = 1, so their sum is v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-cyclic-covariant-universal-property"),
                Handle("cyclic_covariant_universal_property"),
                H("Existence and uniqueness on the full continuous carrier"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Bang, Sp, F.Id("L"), Colon, Sp,
                    Sub(F.Id("B"), F.Id("M")), Sp, To, Sp, F.Id("B"), Comma, Sp,
                    Open, Forall, Sp, F.Id("f"), Comma, Sp,
                    Call(F.Id("L"), Call(F.Id("D"), F.Id("f"))), Sp, Eq, Sp,
                    Call(Pi, F.Id("f")), Close, Sp, Land, Sp,
                    Call(F.Id("L"), Sub(F.Id("S"), F.Id("M"))), Sp, Eq, Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The quantified L is a unital complex star homomorphism. The direct "
                        + "field lift supplies existence for every covariant pair above. "
                        + "There is no additional assumption that v^M is one.")),
                    Paragraph(Text(
                        "For uniqueness, the original S_M^i D(delta_0) (S_M^j)* are exactly "
                        + "the constant standard matrix units. The cardinal power S_M^M "
                        + "is the scalar coordinate field. Stone-Weierstrass uniqueness, "
                        + "transported by the parameter homeomorphism, determines a scalar "
                        + "continuous-function homomorphism from that coordinate. Finite "
                        + "entry reconstruction then determines the homomorphism on every "
                        + "continuous matrix field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-covariant-model-and-closed-generation"),
                Handle("cyclic_covariant_model"),
                H("Faithful readouts and closed generation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call(Op("Injective"), F.Id("D")), Sp, Land, Sp,
                    Sub(F.Id("S"), F.Id("M")), Sp, InMacro, Sp,
                    Call(F.Id("U"), Sub(F.Id("B"), F.Id("M"))), Sp, Land, Sp,
                    Call(Op("Covariant"), F.Id("D"), Sub(F.Id("S"), F.Id("M"))),
                    Sp, Land, Sp,
                    Overline, Grp(Call(Op("StarAlg"), F.Id("D"), Sub(F.Id("S"), F.Id("M")))),
                    Sp, Eq, Sp, Sub(F.Id("B"), F.Id("M"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Diagonal evaluation proves D injective. The original winding shift "
                    + "is unitary and implements alpha_1 in the stated orientation. Apply "
                    + "the constructed universal property to the closed star subalgebra "
                    + "generated by these elements. Inclusion composed with the resulting "
                    + "lift is the identity by uniqueness, so the subalgebra is all of B_M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unique-isometric-cyclic-crossed-product-comparison"),
                Handle("cyclic_covariant_unique_isomorphism"),
                H("Comparison with any separately universal crossed product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Bang, Sp, Phi, Colon, Sp, F.Id("A"), Sp, Sim, Sp,
                    Sub(F.Id("B"), F.Id("M")), Comma, Sp,
                    Phi, Circ, Iota, Sp, Eq, Sp, F.Id("D"), Sp, Land, Sp,
                    Call(Phi, F.Id("u")), Sp, Eq, Sp, Sub(F.Id("S"), F.Id("M")),
                    Sp, Land, Sp, Call(Op("Isometry"), Phi)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quantified Phi is a complex star-algebra equivalence. "
                    + "Suppose A has a covariant inclusion iota and unitary u and satisfies "
                    + "the full crossed-product universal property. The comparison needs "
                    + "only its universal contracts for targets A and B_M. The universal "
                    + "maps in both directions have identity composites by uniqueness. "
                    + "They give a complex star-algebra equivalence, which is automatically "
                    + "isometric. The equivalence is unique relative to the specified "
                    + "readout, cyclic origin, orientation, and wrap edge."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/ContinuousObservables/CyclicCovariantUniversal." + name);

    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(Formula value, params Formula[] arguments) =>
        new Formula.Apply(value, [.. arguments]);
}
