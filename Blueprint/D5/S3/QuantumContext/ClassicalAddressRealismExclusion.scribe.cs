using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class ClassicalAddressRealismExclusionDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumContext/ClassicalAddressRealismExclusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite projection contexts exclude deterministic classical hidden-address realism.",
        H("Classical Address Realism Excluded by Finite Projection Contexts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-hidden-address-induces-a-global-projection-valuation"),
                DeclarationHandle.Create(LeanPrefix + "address_induces_global_projection_valuation"),
                H("One hidden address induces a global projection valuation"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("ClassicalAddressRealism"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("addressInducesValuation")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The realism premise is independent of the obstruction: it consists of a "
                            + "nonempty hidden-address type, a deterministic binary outcome table "
                            + "on the eighteen ray labels at each address, and one-per-context "
                            + "completeness for all nine tetrads.")),
                    Paragraph(Text(
                        "For a fixed address, choose the ray label representing each actual "
                            + "projection and read the address's outcome table there. The "
                            + "labeled-projection injectivity theorem proves that this choice "
                            + "agrees with every displayed label, so the context-completeness "
                            + "equations become the global projection-valuation equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-global-classical-address-realistic-assignment-exists"),
                DeclarationHandle.Create(LeanPrefix + "classical_address_realism_exclusion"),
                H("No deterministic classical hidden-address model exists"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("ClassicalAddressRealism")), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A classical address-realistic model assigns every one of the eighteen "
                            + "ray labels a definite binary value at each member of a nonempty "
                            + "hidden-address space. Context completeness requires exactly one "
                            + "selected ray in each of the nine displayed tetrads at every "
                            + "address.")),
                    Paragraph(Text(
                        "The bridge theorem first turns any single address into a valuation on "
                            + "the actual ConfigurationProjection subtype. Only then does the "
                            + "proof invoke the frozen projection_valuation_obstruction; the "
                            + "realism premise is not a renamed copy of its conclusion.")),
                    Paragraph(Text(
                        "The conclusion concerns only this explicit finite projection "
                            + "configuration and this context-independent binary assignment law. "
                            + "It makes no claim about arbitrary dimensions, arbitrary operator "
                            + "algebras, locality, or every possible meaning of classical realism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-context-assignment-is-a-near-miss"),
                DeclarationHandle.Create(LeanPrefix + "eight_context_near_miss_cannot_extend"),
                H("The eight-context assignment is a genuine near miss"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("v"), Colon, Sp,
                    F.Id("Fin"), Open, D(1, 8), Close, Sp, To, Sp,
                    F.Id("Fin"), Open, D(2), Close, Comma, Esc,
                    F.Id("v"), Sp, Operatorname, Grp(F.Id("satisfiesFirstEight")), Comma,
                    Sp, Land, Sp, Neg, Sp, F.Id("v"), Sp, Operatorname, Grp(F.Id("satisfiesAllNine")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen eightContextValuation supplies one explicit binary assignment "
                            + "whose totals are one in contexts zero through seven.")),
                    Paragraph(Text(
                        "The same assignment cannot satisfy the ninth context: the frozen parity "
                            + "contradiction rules out all nine equations. This keeps the "
                            + "anti-vacuity witness while making clear that the local witness "
                            + "does not extend to a global valuation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-finite-projection-configuration-is-nonvacuous"),
                DeclarationHandle.Create(LeanPrefix + "projection_configuration_is_nonvacuous"),
                H("The finite projection configuration is nonvacuous"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("Fin")), Open, D(9), Close, Close,
                    Sp, Land, Sp, Open,
                    Forall, Sp, F.Id("c"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("Fin")), Open, D(9), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("projectionContext")), Open,
                    F.Id("c"), Close, Close, Sp, Eq, Sp, D(4), Close,
                    Sp, Land, Sp, Open,
                    Exists, Sp, F.Id("v"), Colon, Sp,
                    Operatorname, Grp(F.Id("ConfigurationProjection")), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Fin")), Open, D(2), Close,
                    Comma, Esc,
                    Sum, Underscore, Grp(
                        F.Id("k"), Sp, InMacro, Sp,
                        Operatorname, Grp(F.Id("Fin")), Open, D(4), Close), Sp,
                    F.Id("v"), Open,
                    Operatorname, Grp(F.Id("labeledProjection")), Open,
                    Operatorname, Grp(F.Id("contextRay")), Open, D(0), Comma, F.Id("k"), Close,
                    Close, Close, Sp, Eq, Sp, D(1), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct exhibits a member of the nine-context index type. "
                            + "The second proves that every context contains exactly four "
                            + "distinct actual projections, using injectivity of both the context "
                            + "ray map and the labeled-projection embedding.")),
                    Paragraph(Text(
                        "For the third conjunct, an explicit binary function assigns one to the "
                            + "first projection of context zero and zero to every other "
                            + "projection. Its sum on that context is one. Thus the contradiction "
                            + "comes from global incompatibility among the nine contexts, not from "
                            + "an empty context family, malformed contexts, or a locally "
                            + "unsatisfiable constraint."))),
                DescribeRole.Theorem))));
}
