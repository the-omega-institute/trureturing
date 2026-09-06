using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class ImmutableExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A frozen prefix code admits exactly the extensions certified by its depth-sensitive residual capacity profile.",
        H("Immutable Prefix-Code Extension"),
        Blocks(
            Paragraph(Text(
                "Residual capacity remembers where frozen words sit in the prefix tree, not only "
                    + "their lengths or total Kraft mass. The first theorem computes that capacity "
                    + "exactly, and the second characterizes every feasible finite request multiset.")),
            Paragraph(Text(
                "In both statements q and n are natural numbers and C is a finite set of lists "
                    + "over Fin q. The request L is a multiset of natural numbers. Compatible(C,w) "
                    + "means that, for every u in C, neither u is a prefix of w nor w is a prefix "
                    + "of u. The finset freeAt(C,n) consists of the length-n vectors whose lists "
                    + "satisfy this condition. The function demand(q,L,n) sums q^(n-l) over all "
                    + "occurrences of l in L with l at most n.")),
            Paragraph(Text(
                "Extends(C,L,xs) means that xs has no duplicate words, C is disjoint from "
                    + "xs.toFinset, the multiset of word lengths in xs equals L, and the union "
                    + "of C with xs.toFinset is prefix-free. The shadow identity has no lower "
                    + "bound on q; only the extension criterion assumes q at least two.")),
            Describe.Lean(
                DescribeId.Create("immutable-extension-shadow-identity"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/ImmutableExtension.freeAt_shadow_identity"),
                H("Exact residual-capacity shadow identity"),
                StatementSource.FromAuthor(ShadowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At depth n, all q^n words split into three classes: slots compatible "
                            + "with the frozen code, descendants of frozen words of length at most "
                            + "n, and depth-n prefixes of longer frozen words.")),
                    Paragraph(Text(
                        "The last term is the cardinality of the image finset longPrefixes. Thus "
                            + "different long frozen words sharing the same depth-n prefix consume "
                            + "that slot once, which is the exact correction missing from a union bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("immutable-extension-depth-capacity-criterion"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/ImmutableExtension.extension_iff_depth_capacity"),
                H("Depth capacity exactly characterizes immutable extension"),
                StatementSource.FromAuthor(ExtensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a prefix-free code over q symbols, with q at least two, and let L "
                            + "be a multiset of requested new lengths. An exact extension exists if "
                            + "and only if the multiplicity-sensitive demand at every requested depth "
                            + "does not exceed the number of slots compatible with C.")),
                    Paragraph(Text(
                        "Necessity counts disjoint cylinders of the requested words inside freeAt. "
                            + "For sufficiency, sort the requests and add a word at each new maximum "
                            + "depth; exact cylinder accounting supplies a free slot. Requests may be "
                            + "shorter than frozen words, and no frozen word is replaced."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PrefixFreeCode")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/KraftConverse"))]));

    private static Formula ShadowFormula()
    {
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula c = F.Id("C");
        Formula u = F.Id("u");
        Formula shortCondition = F.Seq(
            u, Sp, InMacro, Sp, c, Comma, Sp, Call("length", u), Sp, Leq, Sp, n);
        Formula shortCapacity = F.Seq(
            Sum, Underscore, Grp(shortCondition), Sp,
            new Formula.Power(q, Grp(n, Sp, Minus, Sp, Call("length", u))));

        return Disp(Seq(
            Forall, Sp, q, Comma, Sp, n, Comma, Sp, c, Comma, Sp,
            Call("IsPrefixFree", c), Sp, Rightarrow, Sp,
            Cardinality(Call("freeAt", c, n)), Sp, Plus, Sp,
            shortCapacity, Sp, Plus, Sp,
            Cardinality(Call("longPrefixes", c, n)), Sp, Eq, Sp,
            new Formula.Power(q, n), Dot));
    }

    private static Formula ExtensionFormula()
    {
        Formula q = F.Id("q");
        Formula c = F.Id("C");
        Formula l = F.Id("L");
        Formula n = F.Id("n");
        Formula xs = F.Id("xs");

        return Disp(Seq(
            Forall, Sp, q, Comma, Sp, c, Comma, Sp, l, Comma, Sp,
            D(2), Sp, Leq, Sp, q, Comma, Sp,
            Call("IsPrefixFree", c), Sp, Rightarrow, Sp,
            Open, Exists, Sp, xs, Comma, Sp, Call("Extends", c, l, xs), Close,
            Sp, Leftrightarrow, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, l, Comma, Sp,
            Call("demand", q, l, n), Sp, Leq, Sp,
            Cardinality(Call("freeAt", c, n)), Dot));
    }

    private static Formula Cardinality(Formula value) =>
        F.Seq(F.Vert, value, F.Vert);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
