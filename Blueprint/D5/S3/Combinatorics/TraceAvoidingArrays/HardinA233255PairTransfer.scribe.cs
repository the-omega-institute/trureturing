using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal seven-column arrays and the exact transfer on labelled six-cell boundaries.",
        H("Positive-height arrays with horizontal and antidiagonal bonds"),
        Blocks(
            Paragraph(Text("Source problem: R. H. Hardin, OEIS A233255, "
                + "https://oeis.org/A233255 (OEIS licence: https://oeis.org/LICENSE). "
                + "The all-height labelled count correspondence below is one part of the "
                + "literal count to canonical-shape transfer argument.")),
            Paragraph(Text("An array is an individual function on a positive number of rows and "
                + "seven columns with values in six colours. Its upper-left colour is zero. "
                + "Only horizontal and upper-right/lower-left antidiagonal bonds exclude equal "
                + "colours and colours whose sum is five. In row-major order each colour two, "
                + "three, or four requires an earlier one, and each three requires an earlier two. "
                + "Missing colours are allowed. No zero-height sequence value is defined.")),
            Node("Row", "Colour rows", "Seven ordered individual colours.", DescribeRole.Definition),
            Node("PairRow", "Pair-label rows", "Seven ordered complementary-pair labels.", DescribeRole.Definition),
            Node("Boundary", "Labelled boundaries", "The six labels in columns one through six.",
                DescribeRole.Definition),
            Node("rowLegal", "Horizontal exclusions", "Every adjacent horizontal bond is tested.",
                DescribeRole.Definition),
            Node("bonds", "Antidiagonal exclusions", "The preceding column j+1 is bonded to the next column j.",
                DescribeRole.Definition),
            Node("Legal", "The literal array predicate", "The existing HardinA233251TriangleStrip.widthLegal "
                + "is applied at width seven with rowLegal and bonds. Its scanner normalization uses strict earlier cells.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidablerowlegal"),
                DeclarationHandle.Create(Prefix + "decidableRowLegal"),
                H("Decidability of horizontal exclusions"),
                StatementSource.FromAuthor(Disp(DecidableRowLegalFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The instance decides the six adjacent horizontal bonds by finite "
                    + "universal quantification and decidable conjunction. Fin.val explicitly reads each "
                    + "colour as a natural number."))), DescribeRole.Definition),
            Node("a", "The positive-height literal count", "The filter ranges over individual arrays without a quotient.",
                DescribeRole.Definition),
            Node("pairs", "The preceding boundary", "Apply the existing complementary-pair map after discarding column zero.",
                DescribeRole.Definition),
            Node("compatible", "The literal next-row bond test", "Every preceding boundary label excludes its bonded next-row label.",
                DescribeRole.Definition),
            Node("rowProper", "Proper pair words", "Consecutive labels differ.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidablerowproper"),
                DeclarationHandle.Create(Prefix + "decidableRowProper"),
                H("Decidability of proper pair words"),
                StatementSource.FromAuthor(Disp(DecidableRowProperFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The instance decides the six adjacent inequalities of a seven-label "
                    + "word. Such words also form the full boundaries of seven-column square strips."))),
                DescribeRole.Definition),
            Node("labelCompatible", "Compatible pair words", "The six cross-row exclusions are expressed in pair labels.",
                DescribeRole.Definition),
            Node("labelBoundary", "The successor boundary", "Discard column zero only after scanning the entire row.",
                DescribeRole.Definition),
            Node("pairV", "The exact labelled continuation transfer", "Each actual pair word is weighted by its scanner fibre. "
                + "The empty continuation has weight one.", DescribeRole.Definition),
            Node("continuation_pair_bridge", "All continuation heights", "Induction on the number of rows replaces the "
                + "individual-colour row sum by the exact scanner-fibre sum. Both initial scanner flags remain arbitrary.",
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-fibres"),
                DeclarationHandle.Create(Prefix + "first_fibres"),
                H("The first-row scanner fibres"),
                StatementSource.FromAuthor(Disp(FirstFibresFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer readout of the final scanner state and the full "
                    + "seven-label word, fixing the first individual colour to zero leaves the exact "
                    + "scanner-weighted sum over the remaining six labels. A square-strip first-row "
                    + "class readout can therefore reuse this equality directly."))), DescribeRole.Theorem),
            Node("literal_pair_bridge", "The anchored literal readout", "The existing literal array decomposition and the "
                + "continuation identity give this equality at every positive height. Fixing its first colour to zero "
                + "leaves six pair labels with the exact scanner weight, so the first-row sum also counts individual "
                + "colours. Precisely, for every natural n, a(n+1) is the integer sum over all functions "
                + "q from Fin 6 to Fin 3 of rowWeight((false,false),q) times "
                + "pairV(n,rowFinish((false,false),q),q), with a zero summand unless the word "
                + "obtained by prepending zero to q is proper. Reducing labelled boundaries to "
                + "the sixteen canonical proper shapes and aggregating "
                + "the first-row weights by those shapes are further mathematical obligations; "
                + "this identity asserts no recurrence.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula DecidableRowLegalFormula()
    {
        var c = F.Id("c");
        var j = F.Id("j");
        var left = Apply(c, Apply(Name("Fin.castSucc"), j));
        var right = Apply(c, Apply(Name("Fin.succ"), j));
        var distinct = new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
        var sum = new Formula.Binary(Apply(Name("Fin.val"), left), FormulaBinaryOperator.Add,
            Apply(Name("Fin.val"), right));
        var noncomplementary = new Formula.Relation(Parenthesized(sum),
            FormulaRelationOperator.NotEqual, D(5));
        var predicate = All("j", Apply(Name("Fin"), D(6)), new Formula.Logic(
            Parenthesized(distinct), FormulaLogicOperator.And, Parenthesized(noncomplementary)));
        var instance = Parenthesized(Seq(Apply(Name(LeanPrefix + "decidableRowLegal"), c),
            Sp, Colon, Sp, Apply(Name("Decidable"), Apply(Name(LeanPrefix + "rowLegal"), c))));
        return All("c", Name(LeanPrefix + "Row"), new Formula.Relation(instance,
            FormulaRelationOperator.Equal,
            Apply(Name("inferInstanceAs"), Apply(Name("Decidable"), predicate))));
    }

    private static Formula DecidableRowProperFormula()
    {
        var q = F.Id("q");
        var j = F.Id("j");
        var predicate = All("j", Apply(Name("Fin"), D(6)), new Formula.Relation(
            Apply(q, Apply(Name("Fin.castSucc"), j)), FormulaRelationOperator.NotEqual,
            Apply(q, Apply(Name("Fin.succ"), j))));
        var instance = Typed(Apply(Name(LeanPrefix + "decidableRowProper"), q),
            Apply(Name("Decidable"), Apply(Name(LeanPrefix + "rowProper"), q)));
        return All("q", Name(LeanPrefix + "PairRow"), new Formula.Relation(instance,
            FormulaRelationOperator.Equal,
            Apply(Name("inferInstanceAs"), Apply(Name("Decidable"), predicate))));
    }

    private static Formula FirstFibresFormula()
    {
        const string Scanner = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
        const string Fibres = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.";
        var h = F.Id("H");
        var c = F.Id("c");
        var q = F.Id("q");
        var fin3 = Apply(Name("Fin"), D(3));
        var fin6 = Apply(Name("Fin"), D(6));
        var fin7 = Apply(Name("Fin"), D(7));
        var seen = Name(Scanner + "Seen");
        var integer = Name("Int");
        var initial = Typed(Seq(Open, Name("Bool.false"), Comma, Sp, Name("Bool.false"), Close), seen);
        var anchored = new Formula.Relation(Apply(c, Typed(D(0), fin7)),
            FormulaRelationOperator.Equal, Typed(D(0), fin6));
        var good = Apply(Name(Scanner + "good"), initial, c);
        var condition = new Formula.Logic(Parenthesized(anchored), FormulaLogicOperator.And,
            Parenthesized(good));
        var labels = Fn("j", fin7, Apply(Name("D5.S3.Observer.Separation.BooleanRankThreeK4.beta"),
            Apply(c, F.Id("j"))));
        var readout = Apply(h, Apply(Name(Scanner + "finish"), initial, c), labels);
        var summand = Seq(Name("ite"), Sp, Parenthesized(condition), Sp,
            Parenthesized(readout), Sp, Typed(D(0), integer));
        var left = Sum("c", Name(LeanPrefix + "Row"), summand);
        var right = Sum("q", new Formula.TypeArrow(fin6, fin3), new Formula.Binary(
            Parenthesized(Apply(Name(Fibres + "rowWeight"), initial, q)),
            FormulaBinaryOperator.Multiply,
            Parenthesized(Apply(h, Apply(Name(Fibres + "rowFinish"), initial, q),
                Apply(Name("Fin.cons"), Typed(D(0), fin3), q)))));
        var readoutType = new Formula.TypeArrow(seen,
            new Formula.TypeArrow(Name(LeanPrefix + "PairRow"), integer));
        return All("H", readoutType, new Formula.Relation(Parenthesized(left),
            FormulaRelationOperator.Equal, Parenthesized(right)));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp,
            Parenthesized(body)));

    private static Formula Sum(string name, Formula type, Formula body) =>
        Apply(Name("Finset.sum"), Typed(Name("Finset.univ"), Apply(Name("Finset"), type)),
            Fn(name, type, body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);

    private static Formula Name(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(F.Id(part)));
        }
        return Seq(items.ToArray());
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new System.Collections.Generic.List<Formula> { function };
        foreach (var argument in arguments)
        {
            items.Add(Sp);
            items.Add(Parenthesized(argument));
        }
        return Seq(items.ToArray());
    }
}
