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
                {SumTransactionHash T Acc+H.hash}
            end
        end
    in
        case B
        of bloc(number:N previousHash:PH transactions:Ts hash:H) then
            N+PH+{SumTransactionHash Ts 0}
        else
            raise invalidBlocException end
        end
    end

    
    fun {ComputeEffort T}
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
        {System.show {ComputeEffort tx(value:5000)}}
        %% STUDENT START:
        %% TODO
        %% STUDENT END
        FinalState = nil
        FinalBlockchain = nil
    end
end