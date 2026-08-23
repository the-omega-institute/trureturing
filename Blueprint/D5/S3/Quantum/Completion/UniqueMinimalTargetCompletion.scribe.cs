using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class UniqueMinimalTargetCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Call(string name, params Formula[] arguments)
        {
            var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
            for (var index = 0; index < arguments.Length; index++)
            {
                if (index > 0)
                {
                    items.Add(Comma);
                    items.Add(Sp);
                }
                items.Add(arguments[index]);
            }
            items.Add(Close);
            return Seq([.. items]);
        }

        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula subspace = F.Id("M");
        Formula target = F.Id("x");
        Formula residual = F.Id("r");
        Formula residualLine = new Formula.Subscript(F.Id("L"), residual);
        Formula completion = Seq(subspace, Underscore, Star);
        Formula residualLineDefinition = Call("span", Seq(OpenBrace, residual, CloseBrace));
        Formula projection = Seq(F.Id("P"), Underscore, subspace, Open, target, Close);
        Formula quotient = Seq(completion, Slash, subspace);
        Formula candidates = Seq(OpenBrace,
            F.Id("N"), Colon, Sp, Call("ClosedSubspace", space), Sp, Bar, Sp,
            subspace, Sp, Subseteq, Sp, F.Id("N"), Sp, Land, Sp,
            target, InMacro, Sp, F.Id("N"), CloseBrace);
        Formula statement = Disp(Seq(
            Forall, Sp, scalar, Colon, Sp, Operatorname, Grp(F.Id("RCLike")), Comma, Sp,
            Forall, Sp, space, Colon, Sp, Call("Hilbert", scalar), Comma, Sp,
            Forall, Sp, subspace, Colon, Sp, Call("ClosedSubspace", space), Comma, Sp,
            Forall, Sp, target, InMacro, Sp, space, Comma, Sp,
            Operatorname, Grp(F.Id("let")), Open,
            residual, Sp, Eq, Sp, target, Sp, Minus, Sp, projection, Comma, Sp,
            residualLine, Sp, Eq, Sp, residualLineDefinition, Comma, Sp,
            completion, Sp, Eq, Sp, subspace, Sp, Plus, Sp, residualLine,
            Close, SemiSpace,
            Call("Disjoint", subspace, residualLine), Sp, Land, Sp,
            Call("IsLeast", candidates, completion), Sp, Land, Sp,
            Open, residual, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Call("dim", quotient), Sp, Eq, Sp, D(1), Close, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A projection residual generates the unique minimal closed target completion.",
            H("Unique Minimal Target Completion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("unique-minimal-target-completion"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Completion/UniqueMinimalTargetCompletion."
                            + "unique_minimal_target_completion"),
                    H("The residual line is the unique minimal completion"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let M be a closed subspace of a complete real-or-complex "
                                + "inner-product space and let x be a target vector. The residual "
                                + "is constructed from the canonical orthogonal projection.")),
                        Paragraph(Text(
                            "The residual line is disjoint from M, and their sum is the least "
                                + "closed subspace containing both M and x. This least-property "
                                + "states the claimed uniqueness rather than merely exhibiting "
                                + "a containing subspace.")),
                        Paragraph(Text(
                            "When the residual is nonzero, the canonical relative quotient of "
                                + "the completion by M has dimension one. The proof directly uses "
                                + "the projection residual lemma, closed finite-dimensional sums, "
                                + "the second isomorphism law, and the dimension of a nonzero line."))),
                    DescribeRole.Theorem))));
    }
}
