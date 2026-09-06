using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class FiniteGeneratedPropertyInheritanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three external object laws inherited by finite generators and finitary rules hold on "
            + "their generated closure.",
        H("Finite-Generation Inheritance of Three Object Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-generation-inherits-the-three-object-laws"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/FiniteGeneratedPropertyInheritance."
                    + "finite_generated_property_inheritance"),
                H("Finite generation inherits temporal, unitary, and ledger laws"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Sigma be a finite generation system on internal property objects. "
                            + "Write Three(x) for the conjunction of the external temporal, "
                            + "unitary, and ledgered predicates at x. If every registered "
                            + "generator satisfies Three and every registered finite-arity rule "
                            + "preserves Three on its inputs, every generated object satisfies "
                            + "Three.")),
                    Paragraph(Text(
                        "The proof is structural induction on the Generated derivation. The "
                            + "generator case is exactly the supplied generator law; the rule "
                            + "case applies the preservation law to the induction hypotheses for "
                            + "all finitely many inputs.")),
                    Paragraph(Text(
                        "The three properties remain predicates supplied to the theorem, rather "
                            + "than fields inserted into the object. Their inheritance is "
                            + "therefore proved rather than true by construction. The module "
                            + "reuses the existing InternalProperty carrier and does not repackage "
                            + "the separate fixed-code construction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PropertyObject"))]));

    private static Formula TheoremFormula()
    {
        Formula system = Seq(SigmaLower);
        Formula index = F.Id("i");
        Formula rule = F.Id("r");
        Formula inputIndex = F.Id("j");
        Formula inputs = F.Id("x");
        Formula objectValue = F.Id("y");
        Formula temporal = F.Id("t");
        Formula unitary = F.Id("u");
        Formula ledgered = F.Id("l");
        Formula generator = Call("generator", system, index);
        Formula indexedInput = new Formula.Subscript(inputs, inputIndex);
        Formula constructed = Call("construct", system, rule, inputs);
        Formula three(Formula value) => Grp(Seq(
            Call("t", value), Sp, Land, Sp,
            Call("u", value), Sp, Land, Sp,
            Call("l", value)));

        return Disp(Seq(
            Forall, Sp, system, Colon, Sp,
            Operatorname, Grp(F.Id("FiniteGenerationSystem")), Comma, Sp,
            temporal, Comma, Sp, unitary, Comma, Sp, ledgered, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp, three(generator), Close, Sp, Land, Sp,
            Open, Forall, Sp, rule, Comma, Sp, inputs, Comma, Sp,
            Open, Forall, Sp, inputIndex, Comma, Sp,
            three(indexedInput), Close, Sp, Rightarrow, Sp,
            three(constructed), Close, RowBreak, Grp(),
            Rightarrow, Sp, Forall, Sp, objectValue, Comma, Sp,
            Call("Generated", system, objectValue), Sp, Rightarrow, Sp,
            three(objectValue), Dot));
    }
}
