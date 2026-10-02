using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary consecutive arrows and increasing real breakpoints define actual persistence modules.",
        H("Consecutive Arrows and Right-Continuous Real Cells"),
        Blocks(
            Definition("finite-chain", "FiniteChain", "Raw consecutive arrows",
                "The input is an arbitrary finite sequence of bundled K-vector spaces and adjacent "
                    + "linear maps, including length zero. No composite laws or classifier are assumed."),
            Definition("padded-object", "paddedObject", "Keep the last actual object",
                "For a nonempty sequence, natural indices beyond the input retain the actual last "
                    + "object. For an empty sequence all objects are zero."),
            Definition("padded-arrow", "paddedArrow", "Identity padding, not a terminal zero",
                "Use the given adjacent arrow while a next vertex exists. Afterwards use the identity "
                    + "on the retained object, transported only through object equalities."),
            Definition("chain-functor", "chainFunctor", "Actual composites from the pinned supplier",
                "Functor.ofSequence supplies composites and their laws. Restrict to Fin(n) and use "
                    + "copyObj to recover the original objects exactly; no composition theorem is reproved."),
            Definition("chain-diagram", "chainDiagram", "The finite diagram used by the split construction",
                "The actual composite linear maps and the supplied functor laws form Diagram K V."),
            Definition("zero-prefix-object", "zeroPrefixObject", "A single zero prefix object",
                "Bottom is a zero vector space; an ordinary finite index carries its original space."),
            Definition("zero-prefix", "zeroPrefix", "Extend the actual diagram by zero on the left",
                "From bottom use the zero map. Between actual vertices use their actual composites. "
                    + "There is no object after the last finite index."),
            Definition("breakpoints", "Breakpoints", "Strictly increasing real input points",
                "The finite grid stores real times and strict monotonicity. An empty grid is allowed."),
            Definition("cell", "cell", "The last breakpoint at or before a real time",
                "The finite supremum in WithBot(Fin(n)) selects the last eligible index. It is bottom "
                    + "before the first breakpoint and everywhere for an empty grid."),
            Definition("cell-functor", "cellFunctor", "Monotone real cells",
                "Increasing real time can only add eligible indices, giving a monotone selector functor."),
            Definition("real-module", "realModule", "The actual right-continuous extension",
                "Compose the cell selector with the zero-prefix diagram. Cells include their left "
                    + "breakpoint. The last actual object continues for all later real times."),
            Definition("finite-module", "finiteModule", "The actual finite functor",
                "Embed the original finite indices into WithBot and use the same zero-prefix diagram."),
            Definition("sampling-iso", "samplingIso", "Recover the original diagram by sampling",
                "At every input breakpoint the selector equals the corresponding original index. "
                    + "Whiskering that order-category isomorphism gives the actual natural sampling "
                    + "isomorphism. The empty case requires no chosen breakpoint."),
            Definition("real-family", "realFamily", "Positive intervals from the constructed finite basis",
                "Birth is the basis birth breakpoint. Death is the next breakpoint after the last "
                    + "supported vertex when one exists, and infinity otherwise. Ordered basis supports "
                    + "and strict breakpoint monotonicity prove positivity. These are necessary objects; "
                    + "no new theorem content is credited to coordinate or sequence adapters."))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string heading, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);
}
