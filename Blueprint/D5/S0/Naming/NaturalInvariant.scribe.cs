using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class NaturalInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible quantities across naming interfaces are sections of their value functor.",
        H("Natural Invariants Across Naming Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("natural-invariant-and-constant-witness"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/NaturalInvariant."
                    + "naming_natural_invariant_iff_and_integer_witness"),
                H("Natural invariants are compatible families and admit a constant witness"),
                StatementSource.FromAuthor(NaturalInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Name be the category of admissible naming interfaces and let a "
                        + "quantity functor send each interface to its type of quantities. A "
                        + "cross-naming trace is a dependent family with one quantity at every "
                        + "interface. Membership in the functor's sections is definitionally "
                        + "equivalent to compatibility with every refinement morphism: pushing "
                        + "the fine-interface value forward gives the coarse-interface value.")),
                    Paragraph(Text(
                        "The statement uses Mathlib's Functor.sections as the lightweight explicit "
                        + "form of a categorical compatible family. This records the source atom's "
                        + "naturality condition without adding uniqueness, cofilteredness, "
                        + "finiteness, or quantitative hypotheses not present in the source.")),
                    Paragraph(Text(
                        "The definition is inhabited nontrivially: the constant functor with value "
                        + "the integers has the section taking every naming interface to one. The "
                        + "value one makes the witness explicitly nonzero-valued rather than an "
                        + "empty or zero-family artifact.")),
                    Paragraph(Text(
                        "Repository searches found only preorder-indexed inverse-system variants "
                        + "and a finite cofiltered existence theorem. Pinned Mathlib supplies the "
                        + "exact Functor.sections compatibility predicate and Functor.const for the "
                        + "witness, so the Lean proof reuses both primitives directly."))),
                DescribeRole.Theorem)),
        []));

    private static Formula NaturalInvariantFormula()
    {
        Formula name = F.Id("Name");
        Formula quantity = F.Id("Q");
        Formula trace = Phi;
        Formula fine = Seq(F.Id("r"), Underscore, D(2));
        Formula coarse = Seq(F.Id("r"), Underscore, D(1));
        Formula morphism = F.Id("f");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));

        return Disp(Seq(
            Forall, Sp, name, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("Category", name), CloseBracket, Comma, Esc,
            Open,
            Forall, Sp, quantity, Colon, Sp, Call("Functor", name, F.Id("Type")),
            Comma, Sp, trace, Colon, Sp, Prod, Underscore,
            Grp(F.Id("r"), Sp, InMacro, Sp, name), Sp,
            Call("obj", quantity, F.Id("r")), Comma, Esc,
            trace, Sp, InMacro, Sp, Call("sections", quantity), Sp, Iff, Sp,
            Forall, Sp, fine, Comma, Sp, coarse, Colon, Sp, name, Comma, Sp,
            morphism, Colon, Sp, Call("Hom", fine, coarse), Comma, Esc,
            Call("map", quantity, morphism, Call("apply", trace, fine)), Sp,
            Eq, Sp, Call("apply", trace, coarse),
            Close, Sp, Land, Sp, Esc,
            Exists, Sp, trace, Colon, Sp,
            Call("sections", Call("const", name, integers)), Comma, Sp,
            trace, Sp, Eq, Sp,
            Open, F.Id("r"), Sp, Mapsto, Sp, D(1), Close, Dot));
    }
}
