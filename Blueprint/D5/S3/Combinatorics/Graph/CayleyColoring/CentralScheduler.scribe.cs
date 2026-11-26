using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeCentralSchedulerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform ranking gives the same legal terminal-history probabilities as sequential uniform enabled choices.",
        H("The random central coloring daemon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-law"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law"),
                H("Exact terminal-history law"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("A history is accepted when following the free-color policy produces a proper final coloring. Its ranking fiber consists of permutations yielding that ordered mover list. The enabled sets shrink after each actual recoloring, and permuting the ranks of currently enabled vertices preserves the prefix constraints. The product counts the successive enabled choices from the initial conflict graph. An invalid or nonterminal history has an empty fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-complete"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Complete"),
                H("Complete"),
                StatementSource.FromAuthor(Disp(CayleySchedulerComplete())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-enabled"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Enabled"),
                H("Enabled"),
                StatementSource.FromAuthor(Disp(CayleySchedulerEnabled())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-first"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.First"),
                H("First"),
                StatementSource.FromAuthor(Disp(CayleySchedulerFirst())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-free-policy"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.FreePolicy"),
                H("Free Policy"),
                StatementSource.FromAuthor(Disp(CayleySchedulerFreepolicy())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-history-rank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.HistoryRank"),
                H("History Rank"),
                StatementSource.FromAuthor(Disp(CayleySchedulerHistoryrank())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-legal-prefix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalPrefix"),
                H("Legal Prefix"),
                StatementSource.FromAuthor(Disp(CayleySchedulerLegalprefix())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-legal-run"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalRun"),
                H("Legal Run"),
                StatementSource.FromAuthor(Disp(CayleySchedulerLegalrun())),
                AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(Disp(CayleySchedulerLegalrunConstructor1())), new DocumentBlock.DisplayFormula(Disp(CayleySchedulerLegalrunConstructor2()))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-moves"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Moves"),
                H("Moves"),
                StatementSource.FromAuthor(Disp(CayleySchedulerMoves())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-next-rank"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.NextRank"),
                H("Next Rank"),
                StatementSource.FromAuthor(Disp(CayleySchedulerNextrank())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-policy-run"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.PolicyRun"),
                H("Policy Run"),
                StatementSource.FromAuthor(Disp(CayleySchedulerPolicyrun())),
                AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(Disp(CayleySchedulerPolicyrunConstructor1())), new DocumentBlock.DisplayFormula(Disp(CayleySchedulerPolicyrunConstructor2()))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-prefix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Prefix"),
                H("Prefix"),
                StatementSource.FromAuthor(Disp(CayleySchedulerPrefix())),
                AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(Disp(CayleySchedulerPrefixConstructor1())), new DocumentBlock.DisplayFormula(Disp(CayleySchedulerPrefixConstructor2()))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-prefix-legal"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.legal"),
                H("Legal"),
                StatementSource.FromAuthor(Disp(CayleySchedulerPrefixLegal())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-stop"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Stop"),
                H("Stop"),
                StatementSource.FromAuthor(Disp(CayleySchedulerStop())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-active"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.active"),
                H("Active"),
                StatementSource.FromAuthor(Disp(CayleySchedulerActive())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-choice-product"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.choiceProduct"),
                H("Choice Product"),
                StatementSource.FromAuthor(Disp(CayleySchedulerChoiceproduct())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-conflict"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.conflict"),
                H("Conflict"),
                StatementSource.FromAuthor(Disp(CayleySchedulerConflict())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-proper-policy-run"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.proper_policyRun"),
                H("Proper policy Run"),
                StatementSource.FromAuthor(Disp(CayleySchedulerProperPolicyrun())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-ranked-history"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory"),
                H("Ranked History"),
                StatementSource.FromAuthor(Disp(CayleySchedulerRankedhistory())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("Complete histories exist and are unique for the given graph, ranking and live set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-ranked-history-spec"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory_spec"),
                H("Ranked History spec"),
                StatementSource.FromAuthor(Disp(CayleySchedulerRankedhistorySpec())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-ranked-moves-complement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.ranked_moves_complement"),
                H("Ranked moves complement"),
                StatementSource.FromAuthor(Disp(CayleySchedulerRankedMovesComplement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-scheduler-remaining"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.remaining"),
                H("Remaining"),
                StatementSource.FromAuthor(Disp(CayleySchedulerRemaining())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var k = F.Id("K");
        var g = F.Id("G");
        var policy = F.Id("P");
        var c = F.Id("c");
        var l = F.Id("h");
        var accept = Call("LegalTerminal", g, policy, c, l);
        var ranks = Call("RankFiber", g, c, l);
        var product = Call("choiceProduct", Call("conflict", g, c),
            Call("univ", v), l);
        var equation = Equal(Multiply(Call("card", ranks), product),
            Call("card", Call("Perm", v)));
        var invalid = Seq(Neg, Sp, accept, Sp, Implies, Sp, Call("IsEmpty", ranks));
        var law = Seq(Open, accept, Sp, Implies, Sp, equation, Close, Sp,
            Land, Sp, Open, invalid, Close);
        var inputs = All("G", Call("SimpleGraph", v), All("P", Call("FreePolicy", k, g),
            All("c", Arrow(v, k), All("h", Call("List", v), law))));
        return All("V", F.Id("Type"), All("K", F.Id("Type"),
            Seq(Instance("Fintype", v), Instance("LinearOrder", v), inputs)));
    }

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula CayleySchedulerComplete() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("history"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("Complete"), Sp, F.Id("V"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"),
        Close, Sp, Eq, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Prefix"), Sp,
        F.Id("G"), Sp, Open, DefinitionDsl.Id("coe"), Sp, DefinitionDsl.Id("rank"), Close, Sp,
        DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Sp, Land, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Stop"), Sp, F.Id("G"), Sp, Open,
        DefinitionDsl.Id("remaining"), Sp, DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Close);

    private static Formula CayleySchedulerEnabled() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Enabled"), Sp, F.Id("V"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("live"), Sp,
        F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Exists, Sp, Open, F.Id("w"),
        Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("active"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"));

    private static Formula CayleySchedulerFirst() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, Iota, Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LT"), Sp, Iota, CloseBracket, Sp, Forall, Sp, Open, F.Id("G"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, F.Id("V"), Sp, To, Sp, Iota, Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("First"), Sp, F.Id("V"), Sp, Iota, Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Enabled"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("v"), Sp, Land, Sp, Forall, Sp, Open, F.Id("w"), Sp, Colon, Sp,
        F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Enabled"),
        Sp, F.Id("G"), Sp, DefinitionDsl.Id("live"), Sp, F.Id("w"), Sp, To, Sp, F.Id("w"), Sp, Neq, Sp,
        F.Id("v"), Sp, To, Sp, DefinitionDsl.Id("rank"), Sp, F.Id("v"), Sp, Lt, Sp,
        DefinitionDsl.Id("rank"), Sp, F.Id("w"));

    private static Formula CayleySchedulerFreepolicy() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("G"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("w"), Close,
        Close, Sp, Eq, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Sp, To, Sp, Open,
        DefinitionDsl.Id("color"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Sp, To, Sp, Open,
        F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Sp, To, Sp, Open, Exists, Sp, Open, F.Id("w"), Sp,
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("color"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Close,
        Sp, To, Sp, OpenBrace, Sp, DefinitionDsl.Id("new"), Sp, Colon, Sp, F.Id("K"), Sp, Sp, Bar, Sp, Sp,
        Forall, Sp, Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, To, Sp, DefinitionDsl.Id("new"), Sp, Neq,
        Sp, DefinitionDsl.Id("color"), Sp, F.Id("w"), Sp, CloseBrace);

    private static Formula CayleySchedulerHistoryrank() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("history"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("HistoryRank"), Sp, F.Id("V"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Sp, Colon, Sp, DefinitionDsl.Id("Type"),
        Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("rank"), Sp, Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"),
        Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp, Open, DefinitionDsl.Id("coe"), Sp,
        DefinitionDsl.Id("rank"), Close, Sp, DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Sp,
        CloseBrace);

    private static Formula CayleySchedulerLegalprefix() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("l"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("LegalPrefix"), Sp, F.Id("V"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("l"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("List"), Dot, DefinitionDsl.Id("recOn"), Sp, Open, DefinitionDsl.Id("motive"), Sp,
        Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Sp, To, Sp, DefinitionDsl.Id("Prop"), Close, Sp, F.Id("l"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Sp, Mapsto, Sp, DefinitionDsl.Id("True"), Close, Sp, Open, DefinitionDsl.Id("fun"), Sp, Open,
        F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Open, F.Id("x"), Sp, Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Sp, Open, DefinitionDsl.Id("rec"), Sp, Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Sp, To, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Open,
        DefinitionDsl.Id("alive"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Sp, Eq, Gt,
        Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Enabled"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("alive"), Sp, F.Id("v"), Sp, Land, Sp, DefinitionDsl.Id("rec"), Sp, Open,
        DefinitionDsl.Id("alive"), Sp, Setminus, Sp, OpenBrace, F.Id("v"), CloseBrace, Close, Close, Sp,
        DefinitionDsl.Id("live"));

    private static Formula CayleySchedulerLegalrunConstructor1() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, F.Id("K"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon,
        Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, Open, DefinitionDsl.Id("color"),
        Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("LegalRun"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("color"), Sp, OpenBracket, CloseBracket, Sp, DefinitionDsl.Id("color"));

    private static Formula CayleySchedulerLegalrunConstructor2() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, F.Id("K"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon,
        Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace,
        DefinitionDsl.Id("color"), Sp, DefinitionDsl.Id("final"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp,
        F.Id("K"), CloseBrace, Sp, OpenBrace, F.Id("v"), Sp, Colon, Sp, F.Id("V"), CloseBrace, Sp,
        OpenBrace, DefinitionDsl.Id("tail"), Sp, Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("new"), Sp, Colon, Sp, F.Id("K"), CloseBrace, Comma, Sp,
        Open, Exists, Sp, Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("color"), Close, Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Close, Sp, To, Sp, Open, Forall, Sp, Open,
        F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp,
        F.Id("v"), Sp, F.Id("w"), Sp, To, Sp, DefinitionDsl.Id("new"), Sp, Neq, Sp,
        DefinitionDsl.Id("color"), Sp, F.Id("w"), Close, Sp, To, Sp, DefinitionDsl.Id("CayleyScheduler"),
        Dot, DefinitionDsl.Id("LegalRun"), Sp, F.Id("G"), Sp, Open, DefinitionDsl.Id("Function"), Dot,
        DefinitionDsl.Id("update"), Sp, DefinitionDsl.Id("color"), Sp, F.Id("v"), Sp,
        DefinitionDsl.Id("new"), Close, Sp, DefinitionDsl.Id("tail"), Sp, DefinitionDsl.Id("final"), Sp, To,
        Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("LegalRun"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("color"), Sp, Open, F.Id("v"), Sp, Colon, Colon, Sp, DefinitionDsl.Id("tail"),
        Close, Sp, DefinitionDsl.Id("final"));

    private static Formula CayleySchedulerLegalrun() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("aTwo"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("aOne"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma,
        Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp,
        DefinitionDsl.Id("LegalRun"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("aTwo"), Sp, DefinitionDsl.Id("aOne"), Sp, F.Id("a"), Sp, Colon, Sp,
        DefinitionDsl.Id("Prop"));

    private static Formula CayleySchedulerMoves() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, Iota, Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LT"), Sp, Iota, CloseBracket, Sp, Forall, Sp, Open, F.Id("G"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, F.Id("V"), Sp, To, Sp, Iota, Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Moves"), Sp, F.Id("V"), Sp, Iota, Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp,
        Exists, Sp, Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("active"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("live"), Close, Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, Land, Sp, DefinitionDsl.Id("rank"), Sp,
        F.Id("v"), Sp, Lt, Sp, DefinitionDsl.Id("rank"), Sp, F.Id("w"));

    private static Formula CayleySchedulerNextrank() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("history"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("NextRank"), Sp, F.Id("V"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("live"), Sp,
        DefinitionDsl.Id("history"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("rank"), Sp, Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"),
        Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp, Open, DefinitionDsl.Id("coe"), Sp,
        DefinitionDsl.Id("rank"), Close, Sp, DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Sp,
        Land, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("First"), Sp, F.Id("G"), Sp,
        Open, DefinitionDsl.Id("coe"), Sp, DefinitionDsl.Id("rank"), Close, Sp, Open,
        DefinitionDsl.Id("remaining"), Sp, DefinitionDsl.Id("live"), Sp, DefinitionDsl.Id("history"), Close,
        Sp, F.Id("v"), Sp, CloseBrace);

    private static Formula CayleySchedulerPolicyrunConstructor1() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, F.Id("K"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon,
        Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace,
        DefinitionDsl.Id("policy"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("G"), CloseBrace, Sp, Open, DefinitionDsl.Id("past"), Sp,
        Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Sp, Open, DefinitionDsl.Id("color"), Sp,
        Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"),
        Dot, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("policy"), Sp,
        DefinitionDsl.Id("past"), Sp, DefinitionDsl.Id("color"), Sp, OpenBracket, CloseBracket, Sp,
        DefinitionDsl.Id("color"));

    private static Formula CayleySchedulerPolicyrunConstructor2() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, F.Id("K"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon,
        Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace,
        DefinitionDsl.Id("policy"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("G"), CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("past"),
        Sp, Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace,
        DefinitionDsl.Id("color"), Sp, DefinitionDsl.Id("final"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp,
        F.Id("K"), CloseBrace, Sp, OpenBrace, F.Id("v"), Sp, Colon, Sp, F.Id("V"), CloseBrace, Sp,
        OpenBrace, DefinitionDsl.Id("tail"), Sp, Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        CloseBrace, Sp, Open, DefinitionDsl.Id("enabled"), Sp, Colon, Sp, Exists, Sp, Open, F.Id("w"), Sp,
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("color"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Close,
        Comma, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("G"),
        Sp, DefinitionDsl.Id("policy"), Sp, Open, DefinitionDsl.Id("past"), Sp, Plus, Plus, Sp, OpenBracket,
        F.Id("v"), CloseBracket, Close, Sp, Open, DefinitionDsl.Id("Function"), Dot,
        DefinitionDsl.Id("update"), Sp, DefinitionDsl.Id("color"), Sp, F.Id("v"), Sp,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("policy"), Sp, DefinitionDsl.Id("past"), Sp,
        DefinitionDsl.Id("color"), Sp, F.Id("v"), Sp, DefinitionDsl.Id("enabled"), Close, Close, Sp,
        DefinitionDsl.Id("tail"), Sp, DefinitionDsl.Id("final"), Sp, To, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("policy"), Sp, DefinitionDsl.Id("past"), Sp, DefinitionDsl.Id("color"), Sp, Open,
        F.Id("v"), Sp, Colon, Colon, Sp, DefinitionDsl.Id("tail"), Close, Sp, DefinitionDsl.Id("final"));

    private static Formula CayleySchedulerPolicyrun() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("policy"), Colon, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("G"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("aThree"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("aTwo"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close,
        Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("aOne"), Colon, Sp, DefinitionDsl.Id("List"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp, F.Id("V"), Sp, To, Sp,
        F.Id("K"), Close, Comma, Sp, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("V"), Sp, F.Id("K"), Sp,
        F.Id("G"), Sp, DefinitionDsl.Id("policy"), Sp, DefinitionDsl.Id("aThree"), Sp,
        DefinitionDsl.Id("aTwo"), Sp, DefinitionDsl.Id("aOne"), Sp, F.Id("a"), Sp, Colon, Sp,
        DefinitionDsl.Id("Prop"));

    private static Formula CayleySchedulerPrefixConstructor1() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, Iota, Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("LT"), Sp, Iota, CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("rank"),
        Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, Iota, CloseBrace, Sp, Open, DefinitionDsl.Id("live"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("rank"), Sp, DefinitionDsl.Id("live"), Sp, OpenBracket, CloseBracket);

    private static Formula CayleySchedulerPrefixConstructor2() =>
        Seq(
        Forall, Sp, OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp,
        OpenBrace, Iota, Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, OpenBracket, Sp,
        DefinitionDsl.Id("LT"), Sp, Iota, CloseBracket, Sp, OpenBrace, F.Id("G"), Sp, Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("rank"),
        Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, Iota, CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("live"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), CloseBrace, Sp, OpenBrace, F.Id("v"), Sp, Colon,
        Sp, F.Id("V"), CloseBrace, Sp, OpenBrace, DefinitionDsl.Id("tail"), Sp, Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), CloseBrace, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"),
        Dot, DefinitionDsl.Id("First"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("v"), Sp, To, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp, Open,
        DefinitionDsl.Id("live"), Sp, Setminus, Sp, OpenBrace, F.Id("v"), CloseBrace, Close, Sp,
        DefinitionDsl.Id("tail"), Sp, To, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, Open, F.Id("v"), Sp, Colon, Colon, Sp, DefinitionDsl.Id("tail"), Close);

    private static Formula CayleySchedulerPrefix() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, Iota, Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LT"), Sp, Iota, CloseBracket, Sp, Forall, Sp, Open, F.Id("G"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, F.Id("V"), Sp, To, Sp, Iota, Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("aOne"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("a"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma, Sp,
        DefinitionDsl.Id("Prefix"), Sp, F.Id("V"), Sp, Iota, Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"),
        Sp, DefinitionDsl.Id("aOne"), Sp, F.Id("a"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"));

    private static Formula CayleySchedulerPrefixLegal() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("l"), Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"), Colon, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Prefix"), Sp, F.Id("G"), Sp, Open,
        DefinitionDsl.Id("coe"), Sp, DefinitionDsl.Id("rank"), Close, Sp, DefinitionDsl.Id("live"), Sp,
        F.Id("l"), Close, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("LegalPrefix"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("live"), Sp, F.Id("l"));

    private static Formula CayleySchedulerStop() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("Stop"), Sp, F.Id("V"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Forall, Sp,
        Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, Neg, Sp,
        DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Enabled"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("v"));

    private static Formula CayleySchedulerActive() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("active"), Sp, F.Id("V"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp,
        Eq, Sp, OpenBrace, Sp, DefinitionDsl.Id("Adj"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp,
        Open, F.Id("v"), Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, F.Id("v"), Sp,
        InMacro, Sp, DefinitionDsl.Id("live"), Sp, Land, Sp, F.Id("w"), Sp, InMacro, Sp,
        DefinitionDsl.Id("live"), Sp, Land, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp,
        F.Id("w"), Sp, CloseBrace);

    private static Formula CayleySchedulerChoiceproduct() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("l"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("choiceProduct"), Sp, F.Id("V"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("live"), Sp, F.Id("l"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq,
        Sp, DefinitionDsl.Id("List"), Dot, DefinitionDsl.Id("recOn"), Sp, Open, DefinitionDsl.Id("motive"),
        Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, F.Id("l"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"),
        Close, Sp, Mapsto, Sp, D(1), Close, Sp, Open, DefinitionDsl.Id("fun"), Sp, Open, F.Id("v"), Sp,
        Colon, Sp, F.Id("V"), Close, Sp, Open, F.Id("x"), Sp, Colon, Sp, DefinitionDsl.Id("List"), Sp,
        F.Id("V"), Close, Sp, Open, DefinitionDsl.Id("rec"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Open, DefinitionDsl.Id("alive"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("Nat"),
        Dot, DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Sp, Sp, Bar,
        Sp, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Enabled"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("alive"), Sp, F.Id("w"), Sp, CloseBrace, Sp, Cdot, Sp, DefinitionDsl.Id("rec"), Sp,
        Open, DefinitionDsl.Id("alive"), Sp, Setminus, Sp, OpenBrace, F.Id("v"), CloseBrace, Close, Close,
        Sp, DefinitionDsl.Id("live"));

    private static Formula CayleySchedulerConflict() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("color"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("conflict"), Sp, F.Id("V"), Sp, F.Id("K"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("color"), Sp, Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp,
        Eq, Sp, OpenBrace, Sp, DefinitionDsl.Id("Adj"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp,
        Open, F.Id("v"), Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, Land, Sp, DefinitionDsl.Id("color"), Sp,
        F.Id("v"), Sp, Eq, Sp, DefinitionDsl.Id("color"), Sp, F.Id("w"), Sp, CloseBrace);

    private static Formula CayleySchedulerProperPolicyrun() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("K"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("DecidableEq"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("policy"), Colon, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("FreePolicy"), Sp, F.Id("G"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("init"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("history"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Comma,
        Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("LegalPrefix"), Sp, Open,
        DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("init"), Close, Sp,
        DefinitionDsl.Id("Set"), Dot, DefinitionDsl.Id("univ"), Sp, DefinitionDsl.Id("history"), Sp, Land,
        Sp, DefinitionDsl.Id("CayleyScheduler"), Dot, DefinitionDsl.Id("Stop"), Sp, Open,
        DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("init"), Close, Sp, Open,
        DefinitionDsl.Id("remaining"), Sp, DefinitionDsl.Id("Set"), Dot, DefinitionDsl.Id("univ"), Sp,
        DefinitionDsl.Id("history"), Close, Sp, Iff, Sp, Exists, Sp, Open, DefinitionDsl.Id("final"), Sp,
        Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("K"), Close, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"),
        Dot, DefinitionDsl.Id("PolicyRun"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("policy"), Sp, OpenBracket,
        CloseBracket, Sp, DefinitionDsl.Id("init"), Sp, DefinitionDsl.Id("history"), Sp,
        DefinitionDsl.Id("final"), Sp, Land, Sp, Forall, Sp, Open, F.Id("v"), Sp, F.Id("w"), Sp, Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Neg, Sp, Open, DefinitionDsl.Id("conflict"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("final"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"));

    private static Formula CayleySchedulerRankedhistory() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("rankedHistory"),
        Sp, F.Id("V"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp, DefinitionDsl.Id("live"), Sp, Colon,
        Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("choose"), Sp,
        Open, DefinitionDsl.Id("fun"), Sp, Open, F.Id("l"), Sp, Colon, Sp, DefinitionDsl.Id("List"), Sp,
        F.Id("V"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("Complete"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("rank"), Sp, DefinitionDsl.Id("live"), Sp, F.Id("l"), Close);

    private static Formula CayleySchedulerRankedhistorySpec() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("live"), Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("CayleyScheduler"), Dot,
        DefinitionDsl.Id("Complete"), Sp, F.Id("G"), Sp, DefinitionDsl.Id("rank"), Sp,
        DefinitionDsl.Id("live"), Sp, Open, DefinitionDsl.Id("rankedHistory"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("rank"), Sp, DefinitionDsl.Id("live"), Close);

    private static Formula CayleySchedulerRankedMovesComplement() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("rank"), Colon, Sp, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("Perm"), Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("rankedHistory"), Sp, F.Id("G"), Sp,
        DefinitionDsl.Id("rank"), Sp, DefinitionDsl.Id("Set"), Dot, DefinitionDsl.Id("univ"), Close, Dot,
        DefinitionDsl.Id("length"), Sp, Eq, Sp, DefinitionDsl.Id("Fintype"), Dot, DefinitionDsl.Id("card"),
        Sp, F.Id("V"), Sp, Minus, Sp, DefinitionDsl.Id("filterCard"), Sp, DefinitionDsl.Id("fun"), Sp, Open,
        F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, Forall, Sp, Open, F.Id("w"), Sp, Colon,
        Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp,
        F.Id("w"), Sp, To, Sp, DefinitionDsl.Id("rank"), Sp, F.Id("w"), Sp, Lt, Sp,
        DefinitionDsl.Id("rank"), Sp, F.Id("v"));

    private static Formula CayleySchedulerRemaining() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("live"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("history"), Colon, Sp, DefinitionDsl.Id("List"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("remaining"), Sp, F.Id("V"), Sp, DefinitionDsl.Id("live"),
        Sp, DefinitionDsl.Id("history"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Sp,
        Eq, Sp, OpenBrace, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Sp, Bar, Sp, F.Id("v"), Sp, InMacro, Sp,
        DefinitionDsl.Id("live"), Sp, Land, Sp, F.Id("v"), Sp, Neg, Sp, InMacro, Sp,
        DefinitionDsl.Id("history"), CloseBrace);
}
