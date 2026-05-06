functor
import
    System
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define

    %% STUDENT START:
    
    fun {TransactionHash T}
        case T
        of tx(block_number:Bn nonce:N hash:H sender:S receiver:R value:V max_effort:Me) then
            (N+S+R+V) mod 1000000
        else
            raise invalidTransactionException end
        end
    end

    
    fun {BlocHash B}
        fun {SumTransactionHash Ts Acc}
            case Ts
            of nil then
                Acc
            [] H|T then
                {SumTransactionHash T Acc+{TransactionHash H}}
            end
        end
    in
        case B
        of bloc(number:N previousHash:PH transactions:Ts hash:H) then
            (N+PH+{SumTransactionHash Ts 0}) mod 1000000
        else
            raise invalidBlocException end
        end
    end

    
    fun {ComputeTransactionEffort T}
        fun {NumberOfDigits N Acc} % Acc=0
            if N div 10 == 0 then
                Acc+1
            else
                {NumberOfDigits N div 10 1+Acc}
            end
        end
        fun {SumPowersOfTwo N Acc} % Acc=0
            fun {Pow A B Acc} % Acc=1
                if B == 0 then
                    Acc
                else
                    {Pow A B-1 Acc*A}
                end
            end
        in
            if N == 0 then
                Acc+1
            else
                {SumPowersOfTwo N-1 Acc+{Pow 2 N 1}}
            end
        end
    in
        {SumPowersOfTwo {NumberOfDigits T.value 0}-1 0}
    end

    fun {ComputeBlocEffort B}
        fun {Aux Ts Acc} % Acc=0
            case Ts
            of nil then
                Acc
            [] H|T then
                {Aux T Acc+{ComputeTransactionEffort H}}
            end
        end
    in
        {Aux B.transactions 0}
    end

    fun {IsTransactionValid T State}
        case T
        of tx(block_number:Bn nonce:N hash:H sender:S receiver:R value:V max_effort:Me) then
            if N \= State.(S).nonce+1 then
                {System.show 'Invalid Transaction : Wrong nonce'}
                false
            elseif H \= {TransactionHash T} then
                {System.show 'Invalid Transaction : Wrong hash'}
                false
            elseif State.(S).balance < V+{ComputeTransactionEffort T} then
                {System.show 'Invalid Transaction : Sender balance too low'}
                false
            elseif V < 0 then
                {System.show 'Invalid Transaction : Value is negative'}
                false
            elseif Me =< 0 then
                {System.show 'Invalid Transaction : Max effort is negative or zero'}
                false
            elseif {ComputeTransactionEffort T} > Me then
                {System.show 'Invalid Transaction : Effort exceeds max effort'}
                false
            else
                true
            end
        else
            {System.show 'Invalid Transaction : Wrong Format'}
            false
        end
    end

    fun {IsBlocValid B LastB} % Transactions validity isn't checked since it needs to be checked when adding the transaction (we don't have the data to verify transactions since the state has changed)
        if B.number \= LastB.number+1 then
            {System.show 'Invalid Bloc : Wrong number'}
            false
        elseif B.previousHash \= LastB.hash then
            {System.show 'Invalid Bloc : Wrong previous hash'}
            false
        elseif B.hash \= {BlocHash B} then
            {System.show {BlocHash B}}
            {System.show 'Invalid Bloc : Wrong hash'}
            false
        elseif {ComputeBlocEffort B} > 300 then
            {System.show 'Invalid Bloc : Effort is bigger than 300'}
            false
        else
            true
        end
    end

    fun {AddUserIfNeeded State Transaction}
        fun {ElementInList L E}
            case L
            of nil then
                false
            [] H|T then
                if H==E then
                    true
                else
                    {ElementInList T E}
                end
            end
        end
    in
        if {ElementInList {Arity State} Transaction.receiver} then
            State
        else
            {AdjoinAt State Transaction.receiver user(balance:0 nonce:0)}
        end
    end

    fun {GetUpdatedState State Transaction} % Reverse the order of the elements inside the state, due to the tail recursive nature of the aux function
        fun {GetUpdatedStateAux State Trans Acc Ari}
            case Ari
            of nil then
                Acc
            [] H|T then
                if H == Trans.sender then
                    {GetUpdatedStateAux State Trans {AdjoinAt Acc H user(balance:(State.(H).balance - Trans.value - {ComputeTransactionEffort Trans}) nonce:Trans.nonce)} T}
                elseif H == Trans.receiver then
                    {GetUpdatedStateAux State Trans {AdjoinAt Acc H user(balance:(State.(H).balance + Trans.value) nonce:State.(H).nonce)} T}
                else
                    {GetUpdatedStateAux State Trans {AdjoinAt Acc H user(balance:State.(H).balance nonce:State.(H).nonce)} T}
                end
            end
        end
    in
        {GetUpdatedStateAux {AddUserIfNeeded State Transaction} Transaction state() {Arity {AddUserIfNeeded State Transaction}}}
    end

    fun {InitState Genesis}
        fun {InitStateAux Genesis Acc Ari}
            case Ari
            of nil then
                Acc
            [] H|T then
                {InitStateAux Genesis {AdjoinAt Acc H user(balance:Genesis.(H) nonce:0)} T}
            end
        end
    in
         {InitStateAux Genesis state() {Arity Genesis}}
    end    

    

    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        fun {DecodeHash H Acc}
            SharelockTable = t(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h 18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p 26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x 34:&y 35:&z 36:& )
            fun {NumberOfDigits N Acc} % Acc=0
                if N div 10 == 0 then
                    Acc+1
                else
                    {NumberOfDigits N div 10 1+Acc}
                end
            end
        in
            if H==0 then
                Acc
            else
                if ({NumberOfDigits H 0} mod 2) == 1 then
                    {DecodeHash (H div 10) Acc}
                else
                    local V Char in
                        V = H mod 100 mod 37
                        if V < 10 then
                            Char = 36
                        else
                            Char = V
                        end
                        {DecodeHash (H div 100) SharelockTable.(Char) | Acc}
                    end
                end
            end
        end
        fun {Concat L1 L2}
            case L1
            of nil then
                case L2
                of nil then
                    nil
                [] H|T then
                    H | {Concat L1 T}
                end 
            [] H|T then
                H | {Concat T L2}
            end     
        end
    in
        case Blockchain
        of nil then
            nil
        [] H|T then
            {Concat {DecodeHash H.hash nil} {Decode T}}
        end
    end


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}        
        fun {ExecuteBlockchainAux State Transactions Num PreviousHash FinalState}
            fun {GetBlock Transactions State NewState TransAcc EffortAcc} % TransAcc should start at nil, EffortAcc should start at 0
                case Transactions
                of nil then
                    NewState = State
                    bloc(number:Num previousHash:PreviousHash transactions:TransAcc hash:{BlocHash bloc(number:Num previousHash:PreviousHash transactions:TransAcc hash:0)})
                [] H|T then
                    % Verify if the transaction is the right block number
                    if H.block_number == Num then
                        % Verify if the transaction is valid
                        if {IsTransactionValid H State} then
                            % Verify if the effort doesn't exceed the max of 300
                            if EffortAcc+{ComputeTransactionEffort H} > 300 then
                                {System.show 'Transaction Skipped (Effort exceeds 300)'}
                                {GetBlock T State NewState TransAcc EffortAcc}
                            else
                                % Add transaction
                                {GetBlock T {GetUpdatedState State H} NewState {List.append TransAcc [H]} EffortAcc+{ComputeTransactionEffort H}}
                            end
                        else
                            {System.show 'Transaction Skipped (Invalid)'}
                            {GetBlock T State NewState TransAcc EffortAcc}
                        end
                    else
                        %{System.show 'Transaction Skipped (Wrong block number)'}
                        {GetBlock T State NewState TransAcc EffortAcc}
                    end
                end
            end

            fun {GetMaxBlockNumber Transactions Acc} % Acc should start at 0
                case Transactions
                of nil then
                    Acc
                [] H|T then
                    if H.block_number > Acc then
                        {GetMaxBlockNumber T H.block_number}
                    else
                        {GetMaxBlockNumber T Acc}
                    end
                end
            end
        in
            if Num > {GetMaxBlockNumber Transactions 0} then
                FinalState = State
                nil
            else
                local NewState Bloc in
                    Bloc = {GetBlock Transactions State NewState nil 0}
                    Bloc|{ExecuteBlockchainAux NewState Transactions Num+1 Bloc.hash FinalState}
                end
            end
        end
    in
        FinalBlockchain = {ExecuteBlockchainAux {InitState GenesisState} Transactions 0 0 FinalState}
    end
end
