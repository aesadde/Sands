{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Types where

import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as Set (empty)
import           CoreSyn
import           DynFlags (unsafeGlobalDynFlags)
import           Outputable
import           TidyPgm
import           Utils
import           Var
import           GHC (DataCon, Type)
import           Data.SafeCopy
import           Data.Typeable
import           Data.Serialize
import           Data.Data hiding (DataType)
import           GHC.Generics hiding (moduleName)

import qualified Stack.Types.Version as S
import qualified Stack.Types.PackageName as S (PackageName,fromCabalPackageName,packageNameText)
import           Data.Set (Set)
import           Language.Haskell.Extension (Extension)

--------------------------------------------------------------------------------
-- A Record For Package --------------------------------------------------------
--------------------------------------------------------------------------------
data Package = Package
  { packageName         :: !Text         -- ^ The Name of the package.
  , packageVersion      :: !Text         -- ^ The version of the package
  , packageDependencies :: !(Set Text)   -- ^ All the dependencies of the package.
  , packageFiles        :: [FilePath]    -- ^ All files in the package
  , includeDirs         :: [FilePath]    -- ^ the include dirs of the package used for setting up GHC
  , packageExtensions   :: [Text]        -- ^ extensions used by the package
  , modules             :: [ModuleInfo]  -- ^ all the modules of the package
  } deriving (Show,Eq,Ord,Typeable,SafeCopy,Generic)

instance Serialize Package


addModule :: Package -> ModuleInfo -> Package
addModule pkg mod = pkg {modules = mod : modules pkg}

epkg :: FilePath -> Package
epkg fpath = Package { packageName = "Empty"
                       , packageVersion = "0.0"
                       , packageDependencies = Set.empty
                       , packageFiles = [fpath]
                       , includeDirs = []
                       , packageExtensions = []
                       , modules = []
                       }

--------------------------------------------------------------------------------
-- A Record for Functions ------------------------------------------------------
--------------------------------------------------------------------------------
data CoreFunc = CoreFunc
  {
    funName       :: !Text
  , funType       :: !Text
  , funDef        :: !Text
  , calls         :: ![Text]       -- ^ the functions this function calls
  , internalCalls :: Int           -- ^ how many times is called inside module
  , externalCalls :: Int           -- ^ how many times is called outside this module
  , calledBy      :: [CoreFunc]    -- ^ functions which call this one
  , modN          :: !Text
  , packageN      :: !Text
  } deriving (Show,Eq,Ord,Typeable,SafeCopy,Generic,Data)

instance Serialize CoreFunc


data DataType = NewType | Data | Synonym | ClassInst | OtherData
  deriving (Show,Eq,Ord,Typeable,Data,SafeCopy,Generic)

instance Serialize DataType

--------------------------------------------------------------------------------
-- A Record for Modules ------------------------------------------------------
--------------------------------------------------------------------------------
data ModuleInfo = ModuleInfo
  {
    moduleName :: Text
  , imports    :: [Text]               -- ^ the imports of this module
  , dataDefs   :: [([Text],DataType)]  -- ^ the data definitions of this module
  -- , functions  :: Map Text CoreFunc
  , functions  :: [CoreFunc]
  , contents   :: [Text]-- ^ The core of the module
  } deriving (Show,Eq,Ord,Typeable,SafeCopy,Generic,Data)

emptyModuleInfo :: ModuleInfo
emptyModuleInfo = ModuleInfo
  {
    moduleName = "Empty"
  , imports    = []
  , dataDefs   = []
  , functions  = []
  , contents   = []
  }

instance Serialize ModuleInfo

instance Serialize Text where
  put txt = put $ T.encodeUtf8 txt
  get     = fmap T.decodeUtf8 get


instance Show DataCon where
  show = pprCore

instance Show Var where
  show = pprCore

instance Show CoreBind where
  show = pprCore

instance (OutputableBndr b,Outputable b) => Show (Expr b) where
  show = pprCore

