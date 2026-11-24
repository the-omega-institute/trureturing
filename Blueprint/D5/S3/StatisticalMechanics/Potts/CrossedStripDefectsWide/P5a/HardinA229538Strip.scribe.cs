using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229538StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical one-defect colourings of five-row HDA arrays", H("Canonical one-defect colourings of five-row HDA arrays"), Blocks(
            Paragraph(Text("Colours are introduced in row-major order. At the widths used in the recurrence, the exact defect count excludes constant arrays. Each counted array has six distinct labelled representatives.")),
            Node("canonicalCount",CanonicalCount(),false,"The filter counts arrays of height k and width n with exactly D monochromatic bonds for the cuts H and V and row-major canonical colour introduction."),
            Node("a",Count(),false,"The column-sweep count uses defect budget one."),
            Node("residual",Residual(),false,"Budgets zero and one select the right and left summands respectively."),
            Node("transition_entry",TransitionEntry(),true,"For a budget above one and a positive cost within that budget, the difference of the entries is +1 at the affordable residual successor and −1 at the exhausted successor when the cost is one. The difference is zero in all other cases."),
            Node("labelled_scale",LabelledScale(),true,"The subscript 3 on the literal count is the palette parameter q := 3. The nonconstant arrays contribute six labelled representatives per canonical array. At positive height and width, the three constant arrays contribute one canonical class at budget H.card plus (n − 1) times the sum of the cut cardinalities. At height or width zero, the unique empty array contributes one labelled and one canonical representative at budget zero. The correction is three in the former case and five in the latter."),
            Paragraph(Text("Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.")),
            Node("edges",Edges(),false,"The oriented cut is the disjoint union of the straight pairs and the two orientations of adjacent-row pairs across consecutive columns."),
            Node("mem_edges", MemEdges(), true, "The two inequalities express that the row indices differ by at most one, as in the frozen edge predicate between columns zero and one."),
            Node("cut_total_exclusion", CutTotalExclusion(), true, "A budget differs from the total for every number of cuts exactly when thirteen does not divide it. At height k there are k same-row pairs and k − 1 pairs in each diagonal direction. At height five this gives thirteen pairs."),
            Node("cost",Cost(),false,"The cost is the number of monochromatic bonds on the cut between two decoded columns."),
            Node("bondDefects_empty",BondDefectsEmpty(),true,"For any pair of rows, the empty edge set contributes zero monochromatic bonds."),
            Node("cost_zero",ZeroCost(),true,"A cut has cost zero exactly when every bond has different colours at its endpoints."),
            Node("zero_cost_entry",ZeroCostEntry(),true,"The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds."),
            Node("oneDefect",OneDefect(),false,"Each entry is the indicator of a cut with exactly one monochromatic bond."),
            Node("transfer",Transfer(),false,"The two summands represent one and zero residual defects. A zero-cost cut preserves the budget and a cut of cost one moves from the first summand to the second."),
            Node("terminal",Terminal(),false,"The empty continuation completes an array exactly when its remaining budget is zero."),
            Node("transfer_readout",TransferReadout(),true,"The matrix entries form a semiring, and the independent coefficient action commutes with left multiplication by matrix and readout entries. This lets the matrix action and dot product carry the coefficients through the vector recurrence to give every shifted scalar relation. The commutation law with the right unit also makes the coefficient action distributive. At shift zero a readout supported at a single coordinate recovers that component of the vector recurrence."),
            Node("countCut",CountCut(),false,"The cost counts the colour coincidences at the thirteen oriented pairs of row positions."),
            Node("cost_countCut",CutEquality(),true,"The sum of the thirteen indicators equals the number of monochromatic bonds on the cut."),
            LiteralNode("movesOne", Arrow(Column(), Call("List", Column())), "The Lean definition is the literal vector of 243 successor lists. Applying the vector to a column code selects its list. The theorem moves_one_filter identifies each list with the eligible columns in code order."),
            Node("moves_one_filter",MovesFilter(),true,"Filtering the ordered column codes by cut cost one gives the stored successor list."),
            Node("step_one",StepOne(),true,"The matrix row sums the successor values after multiplying each by one on the left. Left multiplication by zero removes all other entries."),
            Node("weights",Weights(),false,"The first twelve rows come from the identity matrix. The row at exponent twelve appends the proper-colouring coefficients to two zeros. For exponents thirteen through twenty-two, the local literal later in the Lean definition supplies row n minus thirteen. The theorem weights_step pins the rows from exponent twelve onward."),
            Node("weights_step",WeightsStep(),true,"Each index on the right is below the current exponent. The bound proof supplied to Fin.castLE embeds these indices in Fin 23."),
            Node("classIndex",ClassIndex(),false,"The lookup classifies five-entry boundary columns under colour permutation and row reversal."),
            Node("tableOne",TableOne(),false,"The local literal values in the Lean definition has 23 rows and 25 columns. The indices are the exponent n and the class of p. The theorem table_powers pins this lookup through the first summand of the continuation vector."),
            Node("zeroValues",ZeroValues(),false,"For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors."),
            Node("weight_eq",WeightEquality(),true,"The same coefficient formula also holds at the tabulated exponents."),
            Node("zero_values",PowerZero(),true,"The reconstructed value is the proper-colouring continuation vector at each exponent."),
            Node("table_powers",TablePowers(),true,"The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations."),
            Node("coefficients538",Coefficients(),false,"The entries are ordered from the smallest shift of the recurrence to the largest."),
            Node("vector_polynomial",Polynomial(),true,"The relation holds simultaneously for all boundary columns and both residual budgets."),
            Node("result",Recurrence(),true,"The transfer counts labelled arrays by adjacent column cuts. The six-to-one count in labelled_scale identifies that readout with six times a at the widths of the recurrence. Cancelling six in the integer readout gives the order-twenty recurrence for every width at least twenty-three."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229538")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static DocumentBlock LiteralNode(string name, Formula type, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(Typed(Own(name), type))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229538")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; i--)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));
    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
    private static Formula LetLiteral(Formula identifier, Formula type, Formula body) =>
        Parenthesized(Seq(Q("let"), Sp, Typed(identifier, type), Sp, Colon, F.Eq, Sp,
            F.Text, Grp(V("stored"), Sp, V("Lean"), Sp, V("literal")), Sp,
            Q("in"), Sp, Parenthesized(body)));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229538Strip."+n,a);
    private static Formula Count()
    {
        var n = V("n");
        var count = Own("canonicalCount", EmptyCut(Fin(5)), Own("edges"), N(1), n);
        return All("n", Q("Nat"), And(
            Eq(Typed(Own("a", n), Q("Nat")), count),
            Eq(count, FilteredCount(Fin(5), EmptyCut(Fin(5)), CutEdges(), n, N(1)))));
    }

    private static Formula CutEdges() {
        var pairs = Product(Fin(5),Fin(5));
        var r = Val(V("r"));
        var s = Val(V("s"));
        var adjacent = new Formula.Logic(Eq(s,Add(r,N(1))),FormulaLogicOperator.Or,Eq(r,Add(s,N(1))));
        var predicate = new Formula.Logic(Eq(s,r),FormulaLogicOperator.Or,adjacent);
        var filter = Parenthesized(Seq(LambdaLower,Sp,Typed(Pair(V("r"),V("s")),pairs),
            Mapsto,Sp,Parenthesized(predicate)));
        return Call("Finset.filter",filter,Typed(Q("Finset.univ"),Call("Finset",pairs)));
    }

    private static Formula Cuts(Formula index) => Call("Finset", Product(index, index));
    private static Formula EmptyCut(Formula index) => Typed(Q("Finset.empty"), Cuts(index));

    private static Formula FilteredCount(Formula rows, Formula h, Formula v, Formula n, Formula budget) {
        var a=V("A");var cells=Product(rows,Fin(n));
        Formula idx(Formula p)=>Add(Mul(Val(Call("Prod.fst",p)),n),Val(Call("Prod.snd",p)));
        var canonical=All("p",cells,All("c",Fin(3),Imp(Lt(V("c"),App(a,V("p"))),Ex("q",cells,And(Lt(idx(V("q")),idx(V("p"))),Eq(App(a,V("q")),V("c")))))));
        var cols=Call("List.ofFn",Fn("j",Fin(n),Fn("i",rows,App(a,Pair(V("i"),V("j"))))));
        var arrays=Arrow(cells,Fin(3));
        var predicate=Fn("A",arrays,And(Eq(Call("DefectTransfer.defects",h,v,cols),budget),canonical));
        return Call("Finset.card",Call("Finset.filter",predicate,Typed(Q("Finset.univ"),Call("Finset",arrays))));
    }

    private static Formula CutParameters(Formula body) => All("k", Q("Nat"),
        All("H", Cuts(Fin(V("k"))), All("V", Cuts(Fin(V("k"))),
        All("D", Q("Nat"), All("n", Q("Nat"), body)))));

    private static Formula CanonicalCount() => CutParameters(
        Eq(Own("canonicalCount", V("H"), V("V"), V("D"), V("n")),
            FilteredCount(Fin(V("k")), V("H"), V("V"), V("n"), V("D"))));

    private static Formula Recurrence() {
        Formula a(int j)=>AsInt(Own("a",Add(V("n"),N(j))));
        long[] coefficients=[12, 26, -566, -123, 8804, -4121, -59620, 55115, 183692, -256127, -211910, 498819, -48036, -371692, 214008, 43848, -64656, 8640, 5184, -1296];
        Formula rhs=Mul(N(coefficients[0]),a(22));
        for(int i=1;i<coefficients.Length;i++)
            rhs=coefficients[i]<0 ? Sub(rhs,Mul(N(-coefficients[i]),a(22-i)))
                : Add(rhs,Mul(N(coefficients[i]),a(22-i)));
        return All("n",Q("Nat"),Eq(a(23),rhs));
    }

    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Residual()
    {
        var label = V("C");
        var p = V("p");
        var d = V("d");
        return All("C", Seq(Q("Type"), Star), All("p", label, All("d", Q("Nat"),
            Eq(Typed(Own("residual", p, d), Call("Sum", label, label)),
                If(Eq(d, N(0)), Call("Sum.inr", p), Call("Sum.inl", p))))));
    }
    private static Formula TransitionEntry() {
        var p=V("p");var q=V("q");var d=V("d");var s=V("s");
        var cost=Own("cost",p,q);
        var left=If(And(Le(cost,d),Eq(Own("residual",q,Sub(d,cost)),s)),N(1),N(0));
        var rhs=If(Eq(Call("Sum.elim",Q("id"),Q("id"),s),q),Own("transfer",Own("residual",p,d),s),N(0));
        var affordable = And(Lt(N(1), d), And(Lt(N(0), cost), Le(cost, d)));
        var residualEntry = If(Eq(s, Own("residual", q, Sub(d, cost))), N(1), N(0));
        var exhaustedEntry = If(And(Eq(cost, N(1)), Eq(s, Call("Sum.inr", q))), N(1), N(0));
        return All("p", Column(), All("q", Column(), All("d", Q("Nat"), All("s", Columns(),
            Eq(Sub(AsInt(left), rhs), If(affordable, Sub(residualEntry, exhaustedEntry), N(0)))))));
    }

    private static Formula LabelledScale() {
        var k = V("k"); var n = V("n"); var d = V("D"); var h = V("H"); var v = V("V");
        var labelled = App(new Formula.Subscript(Q("DefectTransfer.literalCount"), N(3)), h, v, d, n);
        var hCard = Call("Finset.card", h);
        var constantBudget = Add(hCard, Mul(Call("Nat.pred", n), Add(Call("Finset.card", v), hCard)));
        var correction = If(Or(Eq(k, N(0)), Eq(n, N(0))), If(Eq(d, N(0)), N(5), N(0)),
            If(Eq(d, constantBudget), N(3), N(0)));
        return CutParameters(Eq(Add(labelled, correction), Mul(N(6), Own("canonicalCount", h, v, d, n))));
    }

    private static Formula MemEdges()
    {
        var e = V("e");
        var x = Val(Call("Prod.fst", e));
        var y = Val(Call("Prod.snd", e));
        return All("e", Product(Fin(5), Fin(5)),
            Iff(new Formula.Relation(e, FormulaRelationOperator.MemberOf, Own("edges")),
                And(Le(x, Add(y, N(1))), Le(y, Add(x, N(1))))));
    }

    private static Formula CutTotalExclusion()
    {
        var d = V("D");
        var m = V("m");
        var cutCard = Call("Finset.card", Own("edges"));
        var multiple = new Formula.Relation(N(13), FormulaRelationOperator.Divides, d);
        return All("D", Q("Nat"), Iff(All("m", Q("Nat"), Ne(d, Mul(m, cutCard))),
            Seq(Neg, Sp, Parenthesized(multiple))));
    }

    private static Formula SumOver(string n,Formula t,Formula body) =>
        Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(body));
    private static Formula Pow(Formula a,Formula b) => Seq(Parenthesized(a),Caret,Grp(b));


    private static Formula VectorLiteral(long[] entries)
    {
        Formula tail = Q("Matrix.vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            tail = Call("Matrix.vecCons", N(entries[i]), tail);
        return tail;
    }
    private static Formula Columns() => Call("Sum",Column(),Column());
    private static Formula M(Formula index) => Call("Matrix",index,index,Q("Int"));
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Coefficients() =>
        Eq(Typed(Own("coefficients538"),Arrow(Fin(20),Q("Int"))),VectorLiteral([-1296, 5184, 8640, -64656, 43848, 214008, -371692, -48036, 498819, -211910, -256127, 183692, 55115, -59620, -4121, 8804, -123, -566, 26, 12]));
    private static Formula Polynomial() {
        Formula Power(Formula n)=>Call("Matrix.mulVec",Pow(Own("transfer"),n),Own("terminal"));
        return Eq(Power(N(22)),SumOver("k",Fin(20),
            Call("SMul.smul",Own("coefficients538",V("k")),Power(Add(N(2),Val(V("k")))))));
    }

    private static Formula CountCut() {
        var p=V("p");var q=V("q");
        var bonds=new[]{new[]{0,0},new[]{0,1},new[]{1,0},new[]{1,1},new[]{1,2},new[]{2,1},new[]{2,2},new[]{2,3},new[]{3,2},new[]{3,3},new[]{3,4},new[]{4,3},new[]{4,4}};
        var terms=bonds.Select(e=>If(Eq(C("colour",p,N(e[0])),C("colour",q,N(e[1]))),N(1),N(0)));
        return All("p",Column(),All("q",Column(),Eq(Typed(Own("countCut",p,q),Q("Nat")),terms.Aggregate(Add))));
    }
    private static Formula CutEquality() => All("p",Column(),All("q",Column(),Eq(Own("cost",V("p"),V("q")),
        Own("countCut",V("p"),V("q")))));
    private static Formula Weights()
    {
        var n = V("n");
        var h = V("h");
        var bound = Call("Nat.lt_of_le_of_ne", Call("Nat.le_of_not_gt", h),
            Call("Ne.symm", V("hn")));
        var identityRow = App(Typed(N(1), M(Fin(12))), Call("Fin.castLT", n, h));
        var exceptionalRow = Call("Fin.append", Typed(N(0), Arrow(Fin(2), Q("Int"))), C("coefficients"));
        var later = V("later");
        var laterRow = LetLiteral(later, Arrow(Fin(10), Arrow(Fin(12), new Formula.Integers())),
            App(later, Call("Fin.subNat", N(13), n, bound)));
        return All("n", Fin(23), Eq(Own("weights", n),
            If(Typed(h, Lt(Val(n), N(12))), identityRow,
                If(Typed(V("hn"), Eq(Val(n), N(12))), exceptionalRow, laterRow))));
    }

    private static Formula TableOne()
    {
        var n = V("n");
        var p = V("p");
        var values = V("values");
        var entry = LetLiteral(values, Arrow(Fin(23), Arrow(Fin(25), new Formula.Integers())),
            App(values, n, Own("classIndex", p)));
        return All("n", Fin(23), All("p", Column(), Eq(AsInt(Own("tableOne", n, p)), entry)));
    }

    private static Formula MovesFilter()
    {
        var p = V("p");
        var q = V("q");
        var predicate = Parenthesized(Seq(LambdaLower, Sp, Typed(q, Column()), Mapsto, Sp,
            Call("decide", Eq(Own("cost", p, q), N(1)))));
        return All("p", Column(), Eq(Typed(Own("movesOne", p), Call("List", Column())),
            Call("List.filter", predicate, Call("List.finRange", N(243)))));
    }
    private static Formula StepOne() {
        var scalar = V("R");
        var zeroLeft = All("x", scalar, Eq(Mul(Typed(N(0), scalar), V("x")), Typed(N(0), scalar)));
        var weighted = Fn("q", Column(), Mul(Typed(N(1), scalar), App(V("w"), V("q"))));
        var equation = All("w", Arrow(Column(), scalar), All("p", Column(),
            Eq(Call("dotProduct", Own("oneDefect", V("p")), V("w")),
                Call("List.sum", Call("List.map", weighted, Own("movesOne", V("p")))))));
        return All("R", Seq(Q("Type"), Star), Seq(
            OpenBracket, Call("AddCommMonoid", scalar), CloseBracket, Sp,
            OpenBracket, Call("Mul", scalar), CloseBracket, Sp,
            OpenBracket, Call("One", scalar), CloseBracket, Sp, Imp(zeroLeft, equation)));
    }
    private static Formula WeightsStep()
    {
        var n = V("n");
        var j = V("j");
        var h = V("h");
        var k = V("k");
        var exponent = Val(n);
        var lower = Call("LE.le.trans", Call("Nat.le_add_right", N(10), N(2)), h);
        var bound = Call("Eq.trans_le", Call("Nat.sub_add_cancel", lower),
            Call("Nat.le_of_lt", Call("Fin.isLt", n)));
        var index = Call("Fin.castLE", bound, Call("Fin.natAdd", Sub(exponent, N(10)), k));
        return All("n", Fin(23), All("h", Le(N(12), exponent), All("j", Fin(12),
            Eq(AsInt(Own("weights", n, j)), SumOver("k", Fin(10),
                Mul(C("coefficients", k), Own("weights", index, j)))))));
    }

    private static Formula ClassIndex()
    {
        var p = V("p");
        var decoded = Call("HardinA233178Recurrence.columnEquiv", p);
        var digits = Parenthesized(Seq(App(decoded, N(0)), Comma, Sp, App(decoded, N(1)),
            Comma, Sp, App(decoded, N(2)), Comma, Sp, App(decoded, N(3)), Comma, Sp, App(decoded, N(4))));
        var colorClass = Call("HardinA233260Literal.cls", digits);
        var reversalClass = Typed(VectorLiteral([0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 9, 10, 11, 12, 2, 13, 14, 15, 6, 16, 17, 18, 11, 8, 13, 19, 20, 1, 21, 22, 14, 9, 10, 23, 18, 24, 7, 16, 22, 19, 4]),
            Arrow(Fin(41), Fin(25)));
        return All("p", Column(), Eq(Typed(Own("classIndex", p), Fin(25)), App(reversalClass, colorClass)));
    }

    private static Formula Expansion() => SumOver("j",Fin(12),
        Mul(Own("weights",V("n"),V("j")),C("table",V("j"),V("p"))));
    private static Formula ZeroValues() => All("n",Fin(23),All("p",Column(),Eq(AsInt(Own("zeroValues",V("n"),V("p"))),
        If(Typed(V("h"),Lt(Val(V("n")),N(12))),C("table",Call("Fin.castLT",V("n"),V("h")),V("p")),Expansion()))));
    private static Formula WeightEquality() => All("n",Fin(23),Eq(Own("zeroValues",V("n")),
        SumOver("j",Fin(12),Call("SMul.smul",Own("weights",V("n"),V("j")),C("table",V("j"))))));
    private static Formula OldPower(Formula n) => Call("Matrix.mulVec",Pow(C("T"),n),Typed(N(1),Arrow(Column(),Q("Int"))));
    private static Formula PowerZero() => All("n",Fin(23),Eq(Own("zeroValues",V("n")),OldPower(Val(V("n")))));
    private static Formula TablePowers() {
        var n=V("n");
        return All("n",Fin(23),Eq(Call("Matrix.mulVec",Pow(Own("transfer"),Val(n)),Own("terminal")),
            Call("Sum.elim",Own("tableOne",n),OldPower(Val(n)))));
    }

    private static Formula Edges() {
        var row = Fin(5);
        var straight = Call("Finset.diag", Typed(Q("Finset.univ"), Call("Finset", row)));
        var diagonal = Call("HardinA229637RowColumn.betw", N(5));
        var cut = Call("Finset.union", straight, diagonal);
        return Eq(Typed(Own("edges"), Call("Finset", Product(row, row))), cut);
    }
    private static Formula Cost() {
        Formula Decode(string n)=>Call("HardinA233178Recurrence.columnEquiv",V(n));
        return All("p",Column(),All("q",Column(),Eq(Typed(Own("cost",V("p"),V("q")),Q("Nat")),
            Call("DefectTransfer.bondDefects",Own("edges"),Decode("p"),Decode("q")))));
    }
    private static Formula BondDefectsEmpty() {
        var k = V("k");
        var row = Arrow(Fin(k), Fin(V("q")));
        var empty = Typed(Q("Finset.empty"), Call("Finset", Product(Fin(k), Fin(k))));
        return All("q", Q("Nat"), All("k", Q("Nat"), All("r", row, All("t", row,
            Eq(Call("DefectTransfer.bondDefects", empty, V("r"), V("t")), N(0))))));
    }
    private static Formula ZeroCost() => All("p",Column(),All("q",Column(),
        new Formula.Logic(Parenthesized(Eq(Own("cost",V("p"),V("q")),N(0))),
            FormulaLogicOperator.Iff,Parenthesized(C("Bond",V("p"),V("q"))))));
    private static Formula ZeroCostEntry() => All("p",Column(),All("q",Column(),
        Eq(If(Eq(Own("cost",V("p"),V("q")),N(0)),AsInt(N(1)),N(0)),C("T",V("p"),V("q")))));
    private static Formula OneDefect() {
        var scalar = V("R");
        var entry = All("p", Column(), All("q", Column(),
            Eq(Typed(Own("oneDefect", V("p"), V("q")), scalar),
                If(Eq(Own("cost", V("p"), V("q")), N(1)), N(1), N(0)))));
        return All("R", Seq(Q("Type"), Star), Seq(
            OpenBracket, Call("Zero", scalar), CloseBracket, Sp,
            OpenBracket, Call("One", scalar), CloseBracket, Sp, entry));
    }
    private static Formula Transfer() => Eq(Typed(Own("transfer"),M(Columns())),
        Call("Matrix.fromBlocks",C("T"),Own("oneDefect"),Typed(N(0),M(Column())),C("T")));
    private static Formula Terminal()
    {
        var left = V("C");
        var right = V("Z");
        var result = V("R");
        var type = Seq(Q("Type"), Star);
        var definition = Eq(Typed(Own("terminal"), Arrow(Call("Sum", left, right), result)),
            Call("Sum.elim", Typed(N(0), Arrow(left, result)), Typed(N(1), Arrow(right, result))));
        var instances = Seq(OpenBracket, Call("Zero", result), CloseBracket, Sp,
            OpenBracket, Call("One", result), CloseBracket, Sp, definition);
        return All("C", type, All("Z", type, All("R", type, instances)));
    }

    private static Formula TransferReadout() {
        var state=V("S");var matrix=V("M");var u=V("u");var v=V("v");
        var d=V("d");var b=V("b");var n=V("n");var j=V("j");
        var index=Call("Fin",d);
        var scalar=V("R");var action=V("K");
        var type=Seq(Q("Type"),Star);
        var vectors=Arrow(state,scalar);
        Formula power(Formula k)=>Call("Matrix.mulVec",Pow(matrix,k),u);
        Formula coefficient()=>new Formula.Apply(V("c"),[j]);
        Formula read(Formula k)=>Call("dotProduct",v,power(k));
        var premise=Eq(power(Add(b,d)),SumOver("j",index,
            Call("SMul.smul",coefficient(),power(Add(b,Call("Fin.val",j))))));
        var shifted=Add(n,b);
        var conclusion=Eq(read(Add(shifted,d)),SumOver("j",index,
            Call("SMul.smul",coefficient(),read(Add(shifted,Call("Fin.val",j))))));
        var equivalence = Iff(premise, All("v", vectors, All("n", Q("Nat"), conclusion)));
        var parameters = All("M", Call("Matrix", state, state, scalar), All("u", vectors, All("d", Q("Nat"),
            All("b", Q("Nat"), All("c", Arrow(index, action), equivalence)))));
        return All("S",type,All("R",type,All("K",type,Seq(OpenBracket,Call("Fintype",state),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",state),CloseBracket,Sp,
            OpenBracket,Call("Semiring",scalar),CloseBracket,Sp,
            OpenBracket,Call("SMul",action,scalar),CloseBracket,Sp,
            OpenBracket,Call("SMulCommClass",action,scalar,scalar),CloseBracket,Sp,parameters))));
    }
}
