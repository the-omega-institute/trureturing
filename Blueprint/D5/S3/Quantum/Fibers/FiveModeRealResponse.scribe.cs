using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiveModeRealResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual five-mode protocol responses retain exactly the entrywise real part.",
        H("Five-Mode Real Response Fibers"), Blocks(
            Describe.Lean(DescribeId.Create("five-mode-real-response"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeRealResponse.five_mode_real_response_fiber"),
                H("The exact response fiber and fifteen-dimensional effect span"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Comma, F.Id("Y"), Colon, C("ComplexMatrix", D(5)), Comma,
                    C("Hermitian", F.Id("X")), Land, Sp, C("Hermitian", F.Id("Y")), Rightarrow, Sp,
                    Open, C("AllResponses", F.Id("X")), Eq, C("AllResponses", F.Id("Y")),
                    Leftrightarrow, Sp, C("Re", F.Id("X")), Eq, C("Re", F.Id("Y")), Close, Land, Sp,
                    C("dimR", F.Id("waitSpan")), Eq, D(1, 5), Land, Sp, RowBreak,
                    C("RealSpan", F.Id("AllHistoryEffects")), Eq, F.Id("symmetricEffectSpace"), Land, Sp, RowBreak,
                    Open, Exists, Sp, F.Id("F"), Colon, C("FiniteMatrixSet", D(5)), Comma, C("Finite", F.Id("F")), Land, Sp,
                    F.Id("F"), Subseteq, Sp, F.Id("AllHistoryEffects"), Land, Sp,
                    C("RealSpan", F.Id("F")), Eq, F.Id("symmetricEffectSpace"), Close, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("Seed"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("MeasurableSpace", F.Id("Seed")), CloseBracket, Comma,
                    Forall, Sp, F.Id("mu"), Colon, C("Measure", F.Id("Seed")), Comma,
                    Forall, Sp, F.Id("strategy"), Colon, C("ProtocolFamily", F.Id("Seed"), D(5)), Comma,
                    Forall, Sp, F.Id("event"), Colon, C("FiniteEventFamily", F.Id("strategy")), Comma,
                    C("Re", F.Id("X")), Eq, C("Re", F.Id("Y")), Rightarrow, Sp,
                    C("randomEventProbability", F.Id("mu"), F.Id("strategy"), F.Id("event"), F.Id("X")), Eq,
                    C("randomEventProbability", F.Id("mu"), F.Id("strategy"), F.Id("event"), F.Id("Y")), Close, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("Z"), Colon, C("ComplexMatrix", D(5)), Comma, C("PSD", F.Id("Z")), Rightarrow, Sp,
                    C("AllResponses", C("symmetrize", F.Id("Z"))), Eq, C("AllResponses", F.Id("Z")), Close,
                    Land, Sp, Neg, Sp, C("CP", F.Id("symmetrize")), Land, Sp,
                    C("finiteOrthogonalReadout", F.Id("AllResponses"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The wait is the entrywise complex embedding of exp(t A), for arbitrary nonnegative real t. These waits satisfy the semigroup and unitary identities. Every finite feedback tree, including Stop, is evaluated by the actual complex Lueders recursion.")),
                    Paragraph(Text("For any two Hermitian matrices, equality on every retained protocol history is equivalent to entrywise real-part equality. Each operational history probability is paired with its explicit Heisenberg effect. The full-protocol to first-read span correspondence and the nonnegative-time symmetric spanning theorem prove that the real span of all actual history effects is exactly the entrywise complex embedding of the real symmetric matrices. A finite subset of actual history effects is proved to span this same space, by finite generation and finite support inside the actual family. Adjoining the actual Stop effect and reindexing produces a nonempty finite vector of actual effects, each positive and bounded by the identity. The finiteOrthogonalReadout clause identifies the entire menu fiber with this finite trace readout, its centered invisible residual, and its visible orthogonal projection, by applying ReadoutOrthogonalEquivalence to the actual supplier. The residual and projection equivalences are asserted on positive trace-one states; the entrywise-real equivalence holds on all Hermitian inputs. Upper-triangular coordinates give effect dimension fifteen. Transpose symmetrization preserves every actual menu response on positive inputs, while its Choi obstruction excludes complete positivity. The response equality also persists after integrating any seed-dependent finite recorded event against any input-independent seed measure, with randomEventProbability defined as the Bochner integral of the finite-history event weight. It represents a probability for a probability seed measure and a measurable event-probability function; the integral equality itself also holds for arbitrary seed measures."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-full-rank-blind-neighborhood"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeRealResponse.full_rank_blind_fiber_neighborhood"),
                H("Ten blind directions form a physical neighborhood at full rank"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Rho, Colon, C("ComplexMatrix", D(5)), Comma, C("PosDef", Rho), Land, Sp, C("Tr", Rho), Eq, D(1),
                    Rightarrow, Sp, C("dimR", F.Id("blindDirections")), Eq, D(1, 0), Land, Sp,
                    C("dimR", F.Id("normalizedVisibleDirections")), Eq, D(1, 4), Land, Sp,
                    C("dimR", C("traceZeroHermitian", D(5))), Eq, D(2, 4), Land, Sp, RowBreak,
                    Exists, Sp, F.Id("r"), InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma,
                    F.Id("r"), Gt, D(0), Land, Sp, Forall, Sp, F.Id("D"), InMacro, Sp,
                    F.Id("blindDirections"), Comma, C("CStarNorm", F.Id("D")), Lt, F.Id("r"), Rightarrow, Sp,
                    C("PSD", Seq(Rho, Plus, F.Id("D"))), Land, Sp,
                    C("Tr", Seq(Rho, Plus, F.Id("D"))), Eq, D(1), Land, Sp,
                    C("AllResponses", Rho), Eq, C("AllResponses", Seq(Rho, Plus, F.Id("D")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the real Hermitian input space the real-coordinate map is onto the symmetric effects, so its kernel has dimension ten. The trace-one response directions have dimension fourteen, while the ambient trace-zero Hermitian directions have dimension twenty-four. The ambient dimension is the Hermitian dimension formula of BipartiteSectorDecomposition.")),
                    Paragraph(Text("For a positive-definite trace-one input, a strictly positive spectral lower bound gives a positive radius. Every blind perturbation smaller than this radius remains positive, retains trace one, and has exactly the same finite protocol responses. This establishes a relative neighborhood in all ten linear blind directions. Positive definiteness is essential to this local physical statement; the theorem makes no such neighborhood claim at rank-deficient states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-orthogonal-pair"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeRealResponse.orthogonal_pair_same_actual_responses"),
                H("Orthogonal pure states with identical actual menu responses"),
                StatementSource.FromAuthor(Disp(Seq(
                    C("Density", C("pairState", D(1))), Land, Sp, C("Density", C("pairState", Seq(Minus, D(1)))), Land, Sp,
                    C("pairState", D(1)), C("pairState", Seq(Minus, D(1))), Eq, D(0), Land, Sp,
                    C("pairState", D(1)), Neq, Sp, C("pairState", Seq(Minus, D(1))), Land, Sp,
                    C("AllResponses", C("pairState", D(1))), Eq, C("AllResponses", C("pairState", Seq(Minus, D(1))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two normalized rank-one states lie on the rays e_N plus i e_2 and e_N minus i e_2. Their matrices are one half of the corresponding unnormalized outer products. The proof checks positivity, trace one, zero product, and distinctness, then consumes the full real-response fiber theorem to obtain equality for every actual finite protocol.")),
                    Paragraph(Text("Measurement-relative compression is prior work of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. A response quotient and invisible state directions do not supply a completely positive compression channel. No novelty or optimality claim is made."))), DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
