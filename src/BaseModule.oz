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
            N+PH+{SumTransactionHash Ts 0} mod 1000000
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
            elseif State.(S).balance < V then
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

    fun {GetUpdatedState State Transaction} % Reverse the order of the elements inside the state, due to the tail recursive nature of the aux function
        fun {GetUpdatedStateAux State Trans Acc Arr}
            case Arr
            of nil then
                Acc
            [] H|T then
                if H == Trans.sender then
                    {GetUpdatedStateAux State Trans (user(balance:(State.(H).balance - Trans.value) nonce:Trans.nonce) | Acc) T} % The return value should be a record not a list, but how to append an element ??
                elseif H == Trans.receiver then
                    {GetUpdatedStateAux State Trans (user(balance:(State.(H).balance + Trans.value) nonce:State.(H).nonce) | Acc) T} % The return value should be a record not a list, but how to append an element ??
                else
                    {GetUpdatedStateAux State Trans (user(balance:State.(H).balance nonce:State.(H).nonce) | Acc) T} % The return value should be a record not a list, but how to append an element ??
                end
            end
        end
    in
        {GetUpdatedStateAux State Transaction nil {Arity State}}
    end

    

    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        %% STUDENT START:
        %% TODO
        %% STUDENT END
        nil
    end


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        local Tr1=tx(nonce:5 block_number:1 hash:564 sender:1 receiver:2 value:556 max_effort:7)   Tr2=tx(nonce:6 block_number:2 hash:565 sender:1 receiver:2 value:556 max_effort:7) in
            {System.show {IsTransactionValid Tr1 state(user(balance:600 nonce:4) user(balance:10 nonce:1))}}
            local B=bloc(number:2 previousHash:6 transactions:Tr1|Tr2|nil hash:8+564+565) in
                {System.show {ComputeBlocEffort B}}
                {System.show {IsBlocValid B bloc(number:1 previousHash:0 transactions:nil hash:6)}}
            end
        end
        local State=state(1:user(balance:100 nonce:2) 4:user(balance:500 nonce:3)) in
            local Tr1=tx(nonce:3 block_number:1 hash:564 sender:1 receiver:4 value:55 max_effort:7) in
                {System.show {GetUpdatedState State Tr1}}
            end
        end
        %% STUDENT START:
        %% TODO
        %% STUDENT END
        FinalState = nil
        FinalBlockchain = nil
    end
end
